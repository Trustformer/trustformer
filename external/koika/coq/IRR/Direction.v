(*! Utilities | Refer to positions in a Sact !*)
Require Import Koika.IRR.IRR.
Require Import Coq.Lists.List.

Inductive direction := branch1 | branch2 | branch3.
Scheme Equality for direction.
Definition position := list direction.
Scheme Equality for list.
Definition position_beq := list_beq direction direction_beq.
