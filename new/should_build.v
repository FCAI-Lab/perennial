(** this file references all perennial files that could be used
by other projects.
it serves as a target for [perennial-cli install --vos].
in contrast, CI and [make install] build all .v files in the repo. *)

(* helpers. *)
From New Require ghost.
From Perennial.Helpers Require
  byte_explode bytes ByteString condition CountableTactics finite
  Fractional gmap_algebra gset Integers ipm iris List ListLen ListSolver
  ListSplice ListSubset ListZ LittleEndian Map ModArith NamedProps
  NatDivMod ProofCaching PropRestore Qextra range_set Tactics Transitions.

(* stdlib. *)
From New.proof Require Import
  bytes context errors fmt io log math runtime slices sort strings
  sync time unsafe.
From New.proof.crypto Require Import ed25519.
From New.proof.encoding Require Import binary.
From New.proof.internal Require Import race synctest.
From New.proof.math Require Import bits.
From New.golang.theory.chan.idioms Require idioms.

From New.generatedproof Require math.rand testing.

(* ffi. *)
From Perennial.goose_lang.ffi.grove_ffi Require Import adequacy.

(* common external pkgs. *)
From New.proof.github_com.tchajed Require Import marshal.
From New.proof.github_com.goose_lang Require Import primitive std.
From New.proof.github_com.goose_lang.primitive Require Import disk.

(* testdata. *)
From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples Require
  channel_examples.
From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples Require
  unittest semantics.
From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest Require
  generics.

From New.generatedproof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest Require
  externalglobals.

(* misc. *)
From New.generatedproof.github_com.stretchr.testify Require assert.
From New.proof Require Import inG_problem.

(* social_media_library *)
From New.code.social_media_library Require Import client common manager wrappers.
