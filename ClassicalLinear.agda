module ClassicalLinear where

infixr 2 _,_

data Type : Set where
  _⨁_  : Type -> Type -> Type
  _⨂_ : Type -> Type -> Type
  _&_ : Type -> Type -> Type
  _¬_ : Type -> Type -> Type
  ⊤ : Type
  ⊥ : Type
  One : Type
  Zero : Type

data List (A : Set) : Set where
  _,_ : A -> List A -> List A
  ∙ : List A

infixr 1 _+_
_+_ : ∀ { A } -> List A -> List A -> List A
∙ + a = a
(v , l) + a = v , (l + a)


Context : Set
Context = List Type


infix 1 _⊢_
data Seq : Set where
  _⊢_ : Context -> Context -> Seq

data ⟨_⟩ : Seq -> Set where
  var : ∀ { a }
      -> ⟨ a , ∙ ⊢ a , ∙ ⟩
  exch : ∀ { Γ Γ' Ω Ω' }
       ->  ⟨ Γ' + Γ ⊢ Ω' + Ω ⟩
       ->  ⟨ Γ + Γ' ⊢ Ω + Ω' ⟩

  ⊤R : ∀ { Γ Ω }
     -> ⟨ Γ ⊢ ⊤ , Ω ⟩
  ⊥L : ∀ { Γ Ω }
     -> ⟨ ⊥ , Γ ⊢ Ω ⟩

  ⨂L : ∀ { Γ Ω A B }
    -> ⟨ A , B , Γ ⊢ Ω ⟩
    -> ⟨ A ⨂ B , Γ ⊢ Ω ⟩

  ⨂R : ∀ { Γ Γ' Ω Ω' A B }
    -> ⟨ Γ ⊢ A , Ω ⟩
    -> ⟨ Γ' ⊢ B , Ω' ⟩
    -> ⟨ Γ + Γ' ⊢ A ⨂ B , Ω + Ω' ⟩

postulate undefined : {A : Set} -> A

cut : ∀ { Γ Γ' Ω Ω' A } -> ⟨ Γ ⊢ A , Ω ⟩ -> ⟨ A , Γ' ⊢ Ω' ⟩ -> ⟨ Γ + Γ'  ⊢ Ω + Ω' ⟩

-- L : Γ₁ ⊢ A , Ω₁
-- R : Γ₂ ⊢ B , Ω₂
-- S : A , B, Γ ⊢ Ω 
-- cut L S : 
-- ⟨ Γ₁ + Γ₂ ⊢ A ⨂ B , Ω₁ + Ω₂ ⟩ -> ⟨ A ⨂ B , Γ ⊢ Ω ⟩ -> ⟨ Γ₁ + Γ₂ + Γ  ⊢ Ω₁ + Ω₂ + Ω ⟩
--cut (⨂R L R) (⨂L S) = _ -- exch (cut R (exch (cut L S)))
cut {Γ = Γ + Γ' }  (exch {Γ} {Γ'} { ∙ } { A , Ω } E) V = undefined
cut _ _ = undefined