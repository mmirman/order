module OrderedLogic where

infixr 2 _,_

data Type : Set where
  _~>>_ : Type -> Type -> Type
  _>~>_ : Type -> Type -> Type
  _⨀_ : Type -> Type -> Type
  T : Type

data Context : Set where
  _,_ : Type -> Context -> Context
  ∙ : Context

infixr 1 _+_
_+_ : Context -> Context -> Context
∙ + a = a
(v , l) + a = v , (l + a)


infix 1 _⊢_
data Seq : Set where
  _⊢_ : Context -> Type -> Seq

data ⟨_⟩ : Seq -> Set where
  var : ∀ { a }
      -> ⟨ a , ∙ ⊢ a ⟩

  ~>>R : ∀ { Γ a b }
       -> ⟨ Γ + a , ∙ ⊢ b ⟩
       -> ⟨ Γ ⊢ a ~>> b ⟩

  ~>>L : ∀ { Γ₁ Γ₂ Γ₃ a b c }
       -> ⟨ Γ₂ ⊢ a                     ⟩
       -> ⟨ Γ₁ + b , Γ₃ ⊢ c            ⟩
       -> ⟨ Γ₁ + a ~>> b , Γ₂ + Γ₃ ⊢ c ⟩

  >~>R : ∀ { Γ a b }
       -> ⟨ a , Γ ⊢ b   ⟩
       -> ⟨ Γ ⊢ a >~> b ⟩

  >~>L : ∀ { Γ₁ Γ₂ Γ₃ a b c }
       -> ⟨ Γ₂ ⊢ a                     ⟩
       -> ⟨ Γ₁ + b , Γ₃ ⊢ c            ⟩
       -> ⟨ Γ₁ + Γ₂ + a >~> b , Γ₃ ⊢ c ⟩

  ⨀R : ∀ { Γ₁ Γ₂ a b }
     -> ⟨ Γ₁ ⊢ a          ⟩
     -> ⟨ Γ₂ ⊢ b          ⟩
     -> ⟨ Γ₁ + Γ₂ ⊢ a ⨀ b ⟩

  ⨀L : ∀ { Γ₁ Γ₂ a b c }
     -> ⟨ Γ₁ + a , b , Γ₂ ⊢ c ⟩
     -> ⟨ Γ₁ + a ⨀ b , Γ₂ ⊢ c ⟩

{-
Isorecursive Types:  
 
 Γ ⊢ A : [α / μα.T] T
-----------------------
  Γ ⊢ roll A : μα.T

     Γ ⊢ A : μα.T
-----------------------------
Γ ⊢ unroll A : [α / μα.T] T


     Γ, A ; · ⊢  A
    ---------------- fix
      Γ ; · ⊢  A

     
 Γ, u:A ; · ⊢ P : A
--------------------- fix
Γ ; · ⊢ fix[u] P : A


or

    u:A ⊢ P : A
--------------------- fix
 · ⊢ fix[u] P : A

!thus ensuring only a single recursive instance!


-}



infix 5 _==t_
data _==t_ : Type -> Type -> Set where
  =~>> : ∀ { A B } {A' B'}
       -> A ==t A' 
       -> B ==t B'
       -> A ~>> B ==t A' ~>> B'
  =>~> : ∀ { A B } {A' B'}
       -> A ==t A' 
       -> B ==t B'
       -> A >~> B ==t A' >~> B'
  =⨀ : ∀ { A B } {A' B'}
       -> A ==t A' 
       -> B ==t B'
       -> A ⨀ B ==t A' ⨀ B'
  =T : T ==t T
  =A : ∀ {A} -> A ==t A
infixr 0 _==c_  
data _==c_ : Context -> Context -> Set where
  =, : ∀ {A Γ} {A' Γ'}
     -> A ==t A' 
     -> Γ ==c Γ'
     -> A , Γ ==c A' , Γ'
  =∙ : ∙ ==c ∙

infixr 0 _==p_  
data _==p_ : ∀{A} -> ⟨ A ⟩ -> ∀{B} -> ⟨ B ⟩ -> Set where
  =var : ∀ {a a'}
       -> a ==t a'
       -> var {a} ==p var {a'}

  =~>>R : ∀{Γ a b A}{Γ' a' b' A'}
        -> A ==p A'
        -> ~>>R {Γ} {a} {b} A ==p ~>>R {Γ'} {a'} {b'} A'

  =>~>R : ∀ {Γ a b A}{Γ' a' b' A'}
        -> A ==p A'
        -> >~>R {Γ} {a} {b} A ==p >~>R {Γ'} {a'} {b'} A'

  =~>>L : ∀ {Γ₁ Γ₂ Γ₃ a b c A B}{Γ₁' Γ₂' Γ₃' a' b' c' A' B'}
        -> B ==p B'
        -> A ==p A'
        -> ~>>L {Γ₁} {Γ₂} {Γ₃} {a} {b} {c} A B ==p ~>>L {Γ₁'} {Γ₂'} {Γ₃'} {a'} {b'} {c'} A' B'

  =>~>L : ∀ {Γ₁ Γ₂ Γ₃ a b c A B}{Γ₁' Γ₂' Γ₃' a' b' c' A' B'}
        -> A ==p A'
        -> B ==p B'
        -> >~>L {Γ₁} {Γ₂} {Γ₃} {a} {b} {c} A B ==p >~>L {Γ₁'} {Γ₂'} {Γ₃'} {a'} {b'} {c'} A' B'

  =⨀R : ∀ {Γ₁ Γ₂ a b A B}{Γ₁' Γ₂' a' b' A' B'}
     -> A ==p A'
     -> B ==p B'
     -> ⨀R {Γ₁} {Γ₂} {a} {b} A B ==p ⨀R {Γ₁'} {Γ₂'} {a'} {b'} A' B'

  =⨀L : ∀ {Γ₁ Γ₂ a b c A}{Γ₁' Γ₂' a' b' c' A'}
     -> A ==p A'
     -> ⨀L {Γ₁} {Γ₂} {a} {b} {c} A ==p ⨀L {Γ₁'} {Γ₂'} {a'} {b'} {c'} A'

