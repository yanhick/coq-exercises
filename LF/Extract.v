Require Coq.extraction.Extraction.
Extraction Language Ocaml.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import ImpCEvalFun.

Extraction "imp1.ml" ceval_step.

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant beq_nat => "( = )".

Extract Constant minus => "( - )".

Extraction "imp2.ml" ceval_step.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inductive sumbool => "bool" ["true" "false"].

Require Import Imp.
Require Import ImpParser.

Require Import Maps.
Definition empty_state := { --> 0 }.
Extraction "imp.ml" empty_state ceval_step parse.