--------------------------- MODULE TallestStack3 ---------------------------
(***************************************************************************)
(* You have a stack of n boxes, with widths wi and heights hi, and depths  *)
(* di. The boxes cannot be rotated and can only be stack on top of one     *)
(* another if each box in the stack is strictly larger than the box above  *)
(* it in width, height, and depth. Implement a method to compute the       *)
(* height of the tallest possible stack. The height of a stack is the sum  *)
(* of the heights of each box.                                             *)
(***************************************************************************)

EXTENDS Integers, Sequences

CONSTANTS M, N

ASSUME /\ M \in Nat \ {0}
       /\ N \in Nat \ {0}

GenValues == UNION {[1..N -> 1..M]}

(***************************************************************************)
(* Define a sequence to be sorted in ascending order if for every pair of  *)
(* indices i,j with i < j, the value at index i should be smaller than the *)
(* value at index j.                                                       *)
(***************************************************************************)
SortedAsc(S) == \A i \in 1..Len(S) : \A j \in i..Len(S) : S[i] < S[j]

(*

--fair algorithm TallestStack {
    variables
       i = 1,
       j = 1,
       tmp = 0,
       widths \in GenValues,
       heights \in GenValues,
       depths \in GenValues,
       maxHeight = 0,
       tallestIndex = 1, \* index of stack with maximum height within stacks
       stacks = [x \in 1..N |-> <<x>>], \* sequence of calculated stacks
       m = [x \in 1..N |-> 0]; \* memoisation sequence
       
    macro Swap(i, j, tmp) {
      tmp := heights[i];
      heights[i] := heights[j];
      heights[j] := tmp;
      tmp := widths[i];
      widths[i] := widths[j];
      widths[j] := tmp;
      tmp := depths[i];
      depths[i] := depths[j];
      depths[j] := tmp;
    }
       
    {
        \* sort boxes by height if not already sorted
        if (~SortedAsc(heights)) {
            i := 1;
            while (i <= Len(heights)) {
              j := i;
              while (j > 1 /\ heights[j] < heights[j-1]) {
                Swap(j, j - 1, tmp);
                j := j - 1;
              };
              i := i + 1;
            };
        };
        
        m := heights;
        i := 1;
        while (i <= N) {
            j := 1;
            while (j < i) {
                if ((widths[j] < widths[i] /\ depths[j] < depths[i] /\ heights[j] < heights[i])
                    /\ m[j] + heights[i] > m[i]) {
                    stacks[i] := stacks[j] \o <<i>>;
                    m[i] := heights[i] + m[j];
                };
                j := j + 1;
            };
            if (m[i] > maxHeight) {
                tallestIndex := i;
                maxHeight := m[i];
            };
            i := i + 1;
        };
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "37df0257" /\ chksum(tla) = "9d00c6d")
VARIABLES i, j, tmp, widths, heights, depths, maxHeight, tallestIndex, stacks, 
          m, pc

vars == << i, j, tmp, widths, heights, depths, maxHeight, tallestIndex, 
           stacks, m, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ j = 1
        /\ tmp = 0
        /\ widths \in GenValues
        /\ heights \in GenValues
        /\ depths \in GenValues
        /\ maxHeight = 0
        /\ tallestIndex = 1
        /\ stacks = [x \in 1..N |-> <<x>>]
        /\ m = [x \in 1..N |-> 0]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF ~SortedAsc(heights)
               THEN /\ i' = 1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Lbl_7"
                    /\ i' = i
         /\ UNCHANGED << j, tmp, widths, heights, depths, maxHeight, 
                         tallestIndex, stacks, m >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= Len(heights)
               THEN /\ j' = i
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Lbl_7"
                    /\ j' = j
         /\ UNCHANGED << i, tmp, widths, heights, depths, maxHeight, 
                         tallestIndex, stacks, m >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF j > 1 /\ heights[j] < heights[j-1]
               THEN /\ tmp' = heights[j]
                    /\ heights' = [heights EXCEPT ![j] = heights[(j - 1)]]
                    /\ pc' = "Lbl_4"
                    /\ i' = i
               ELSE /\ i' = i + 1
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED << tmp, heights >>
         /\ UNCHANGED << j, widths, depths, maxHeight, tallestIndex, stacks, m >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ heights' = [heights EXCEPT ![(j - 1)] = tmp]
         /\ tmp' = widths[j]
         /\ widths' = [widths EXCEPT ![j] = widths[(j - 1)]]
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << i, j, depths, maxHeight, tallestIndex, stacks, m >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ widths' = [widths EXCEPT ![(j - 1)] = tmp]
         /\ tmp' = depths[j]
         /\ depths' = [depths EXCEPT ![j] = depths[(j - 1)]]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << i, j, heights, maxHeight, tallestIndex, stacks, m >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ depths' = [depths EXCEPT ![(j - 1)] = tmp]
         /\ j' = j - 1
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << i, tmp, widths, heights, maxHeight, tallestIndex, 
                         stacks, m >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ m' = heights
         /\ i' = 1
         /\ pc' = "Lbl_8"
         /\ UNCHANGED << j, tmp, widths, heights, depths, maxHeight, 
                         tallestIndex, stacks >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ IF i <= N
               THEN /\ j' = 1
                    /\ pc' = "Lbl_9"
               ELSE /\ pc' = "Done"
                    /\ j' = j
         /\ UNCHANGED << i, tmp, widths, heights, depths, maxHeight, 
                         tallestIndex, stacks, m >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ IF j < i
               THEN /\ IF (widths[j] < widths[i] /\ depths[j] < depths[i] /\ heights[j] < heights[i])
                          /\ m[j] + heights[i] > m[i]
                          THEN /\ stacks' = [stacks EXCEPT ![i] = stacks[j] \o <<i>>]
                               /\ m' = [m EXCEPT ![i] = heights[i] + m[j]]
                          ELSE /\ TRUE
                               /\ UNCHANGED << stacks, m >>
                    /\ j' = j + 1
                    /\ pc' = "Lbl_9"
                    /\ UNCHANGED << i, maxHeight, tallestIndex >>
               ELSE /\ IF m[i] > maxHeight
                          THEN /\ tallestIndex' = i
                               /\ maxHeight' = m[i]
                          ELSE /\ TRUE
                               /\ UNCHANGED << maxHeight, tallestIndex >>
                    /\ i' = i + 1
                    /\ pc' = "Lbl_8"
                    /\ UNCHANGED << j, stacks, m >>
         /\ UNCHANGED << tmp, widths, heights, depths >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
           \/ Lbl_8 \/ Lbl_9
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

(***************************************************************************)
(* A box x can only be stacked onto a box y if the latter is strictly      *)
(* larger in all three dimensions.                                         *)
(***************************************************************************)
CanStack(x, y) ==
    widths[x] < widths[y] /\ heights[x] < heights[y] /\ depths[x] < depths[y]

(***************************************************************************)
(* A valid stack is a sequence for which it holds for every box that it    *)
(* can be stacked ontop of its underlying boxes.                           *)
(***************************************************************************)
IsValidStack(S) == \A x \in 1..(Len(S) - 1) : CanStack(S[x], S[x + 1])

(***************************************************************************)
(* Set of all valid stacks of length 1 to N with values from a given       *)
(* sequence.                                                               *)
(***************************************************************************)
ValidStacks(S) == {x \in UNION {[1..n -> S] : n \in 1..N} : IsValidStack(x)}

(***************************************************************************)
(* The height of a given stack is defined as the sum of the heights of     *)
(* its boxes.                                                              *)
(***************************************************************************)
RECURSIVE StackHeight(_)
StackHeight(S) == IF S = << >> THEN 0
                  ELSE heights[Head(S)] + StackHeight(Tail(S))

TypeOK ==
    /\ i \in 1..(N+1)
    /\ j \in 1..(N+1)
    /\ \A s \in 1..Len(stacks) : IsValidStack(stacks[s])

(***************************************************************************)
(* Correctness is given when the maximum height calculated is at least as  *)
(* large as the stackheight of all valid stacks.                           *)
(***************************************************************************)
Correctness == \A x \in ValidStacks(1..N) : StackHeight(x) <= maxHeight

=============================================================================
\* Modification History
\* Last modified Wed Jul 05 17:07:55 CEST 2023 by travn
\* Created Tue May 23 15:59:28 CEST 2023 by travn
