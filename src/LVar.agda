open import Algebra using (Op₁; Op₂)
open import Level using (0ℓ)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)
open import Data.List as List using (List)
open import Data.Product as Product using (∃-syntax)
open import Relation.Binary.Lattice

module LVar (lattice : BoundedLattice 0ℓ 0ℓ 0ℓ) where

open BoundedLattice lattice renaming (Carrier to 𝒟)

variable d d′ : 𝒟

-- * Pretypes and Precontexts

infixr 7 _`⇒_
infixr 9 _`×_

data Pretype : Set where
  `1 : Pretype
  _`⇒_ : Pretype → Pretype → Pretype
  _`×_ : Pretype → Pretype → Pretype
  `𝒯 : Pretype
  `𝒟 : Pretype
  `ℒ : Pretype

variable
  P : Pretype
  Q : Pretype
  R : Pretype

infixl 5 _,_

data Precontext : Set where
  ∅   : Precontext
  _,_ : Precontext → Pretype → Precontext

variable
  Γ  : Precontext
  Γ₁ : Precontext
  Γ₂ : Precontext


-- * Types and Contexts

data Type : Pretype → Set where
  `1 : Type `1
  _`⇒_ : Type P → Type Q → Type (P `⇒ Q)
  _`×_ : Type P → Type Q → Type (P `× Q)
  `𝒯 : Type `𝒯
  `𝒟≤_ : (d : 𝒟) → Type `𝒟
  `ℒ≤_ : (d : 𝒟) → Type `ℒ

variable
  A : Type P
  B : Type Q
  C : Type R

_∨̇_ : (A B : Type P) → Type P
`1 ∨̇ `1 = `1
(A `⇒ B) ∨̇ (A′ `⇒ B′) = (A ∨̇ A′) `⇒ (B ∨̇ B′)
(A `× B) ∨̇ (A′ `× B′) = (A ∨̇ A′) `× (B ∨̇ B′)
`𝒯 ∨̇ `𝒯 = `𝒯
(`𝒟≤ d) ∨̇ (`𝒟≤ d′) = `𝒟≤ (d ∨ d′)
(`ℒ≤ d) ∨̇ (`ℒ≤ d′) = `ℒ≤ (d ∨ d′)

data Context : Precontext → Set where
  ∅   : Context ∅
  _,_ : Context Γ → Type P → Context (Γ , P)

variable
  Δ  : Context Γ
  Δ₁ : Context Γ
  Δ₂ : Context Γ

_∨̅_ : (Δ Δ′ : Context Γ) → Context Γ
∅       ∨̅ ∅         = ∅
(Δ , A) ∨̅ (Δ′ , A′) = (Δ ∨̅ Δ′) , (A ∨̇ A′)


-- * Variables

infix 4 _∋_

data _∋_ : Context Γ → Type P → Set where

  Z : ---------
      Δ , A ∋ A

  S : Δ ∋ A
      ---------
    → Δ , B ∋ A


-- * Terms

infix 4 _⊢_

data _⊢_ : Context Γ → Type P → Set where

  var     : Δ ∋ A
            -----
          → Δ ⊢ A

  lam     : Δ , A ⊢ B
            ----------
          → Δ ⊢ A `⇒ B

  app     : Δ₁ ⊢ A `⇒ B
          → Δ₂ ⊢ A
            -----------
          → Δ₁ ∨̅ Δ₂ ⊢ B

  unit    : ------
            Δ ⊢ `1

  letunit : Δ ⊢ `1
          → Δ ⊢ A
            -----------
          → Δ ⊢ A

  pair    : Δ₁ ⊢ A
          → Δ₂ ⊢ B
            ----------------
          → Δ₁ ∨̅ Δ₂ ⊢ A `× B

  letpair : Δ ⊢ A `× B
          → Δ , A , B ⊢ C
            --------------
          → Δ ⊢ C

  new     : Δ ⊢ `ℒ≤ ⊥

  freeze  : Δ ⊢ `ℒ≤ ⊤ `⇒ `𝒟≤ ⊤

  -- TODO: represent threshold sets, and encode get

  put     : Δ ⊢ `ℒ≤ d `⇒ `𝒟≤ d `⇒ `1

-- -}
-- -}
-- -}
-- -}
-- -}
