
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Functions
open import lib.Int
open Int
open import lib.AdjointEquiv
open import lib.Truncations
open Truncation
open import lib.WrappedPath

import lib.loopspace.Basics
import lib.loopspace.Groupoid
import lib.loopspace.Types
import lib.loopspace.Truncation
import lib.loopspace.OverTypes

module lib.LoopSpace where

  open lib.loopspace.Basics public

  module LoopSpace where
     open lib.loopspace.Groupoid    public
     open lib.loopspace.Types       public
     open lib.loopspace.Truncation  public
     open lib.loopspace.OverTypes   public

