module Language.Type.Semantics where


-- ⟦_⟧entry : (e : TCEntry) → {!!} 
-- ⟦ tvar ♯    ⟧entry = {!!}
-- ⟦ tvar ★    ⟧entry = {!!}
-- ⟦ enum      ⟧entry = {!!}
-- ⟦ struct Ts ⟧entry = {!!}


-- -- ⟦ enum     ⟧entry = Lift _ ℕ
-- -- ⟦ struct n ⟧entry = (Fin n → Set) → List Set


-- -- ⟦_⟧ctx = All ⟦_⟧entry

-- -- Byte = Vec Bool 8

-- -- Tuple : List Set → Set
-- -- Tuple []       = ⊤
-- -- Tuple (A ∷ xs) = A × Tuple xs

-- -- data Tag (tag : String) : Set where
-- --    mkTag : Tag tag 


-- -- -- -- Just assume implementations of some of the ledger types for now. Later, we
-- -- -- -- can replace these with actual implementations.
-- -- -- --
-- -- -- -- It's not unlikely that these implementations would require e.g. decidable
-- -- -- -- equality or other properties of types. There's a couple of optiones: 
-- -- -- --
-- -- -- -- (1) We could define these implementations mutually with the semantics of
-- -- -- --     types and decidable equality. Decidable equality should of course also be
-- -- -- --     available for these implementations, since structures can be nested!
-- -- -- --
-- -- -- --       mutual
-- -- -- --         ⟦_⟧   : Type → Set
-- -- -- --         deceq : Type → Dec ⟦ T ⟧
-- -- -- --
-- -- -- -- (2) We add decidable equality as an instance argument, and construct it
-- -- -- --     on-demand for each type when constructing values in the semantics of a
-- -- -- --     type T. This would look something like the following
-- -- -- --
-- -- -- --       ⟦ SetT T ⟧ = ⦃ _ : DecEq ⟦ T ⟧ ⦄ → SetI ⟦ T ⟧  
-- -- -- --
-- -- -- --     But of course, this would require us to implement decidable equality for
-- -- -- --     Pi types akin to the one above ...
-- -- -- --
-- -- -- --  (3) We could also make decidable equality part of the semantics itself,
-- -- -- --      effectively saying that the semantics of types is sets with dedicable
-- -- -- --      equality.
-- -- -- --
-- -- -- --        ⟦-⟧ : Type → Σ Set DecEq 
-- -- -- --
-- -- -- --      This seems like the most favorable option, as it makes decidable
-- -- -- --      equality for element types available when referring to the
-- -- -- --      implementation of container types, by strengthening the induction
-- -- -- --      hypothesis, while preventing the impossible tangle of dependencies we
-- -- -- --      get when giving types a set semantics and defining decidable equality
-- -- -- --      mutually. 
-- -- -- -- 
-- -- -- module Types (SetI                : Set → Set)
-- -- --              (MapI                : Set → Set → Set)
-- -- --              (MerkleTreeI         : ℕ → Set → Set)
-- -- --              (HistoricMerkleTreeI : ℕ → Set → Set) where 
  

-- -- --   ⟦_⟧T : Type Δ → ⟦ Δ ⟧ctx → Set 
-- -- --   ⟦ Boolean                ⟧T δ = Bool
-- -- --   ⟦ UInteger[<= n ]        ⟧T δ = ∃ λ n′ → n′ ≤ n
-- -- --   ⟦ UInteger[ n ]          ⟧T δ = ∃ λ n′ → n′ ≤ 2 ^ n
-- -- --   ⟦ Field                  ⟧T δ = ℕ
-- -- --   ⟦ Void                   ⟧T δ = ⊤
-- -- --   ⟦ Bytes[ n ]             ⟧T δ = Vec Byte n
-- -- --   ⟦ Vector[ n , T ]        ⟧T δ = Vec (⟦ T ⟧T δ) n
-- -- --   ⟦ Opaque[ s ]            ⟧T δ = Tag s
-- -- --   ⟦ Var x                  ⟧T δ = lookup δ x
-- -- --   ⟦ Enum x                 ⟧T δ = Fin (lookup δ x .lower)
-- -- --   ⟦ Struct x xs            ⟧T δ = Tuple (lookup δ x (flip ⟦_⟧T δ ∘ xs))
-- -- --   ⟦ Counter                ⟧T δ = ℕ
-- -- --   ⟦ Cell T _               ⟧T δ = ⟦ T ⟧T δ
-- -- --   ⟦ SetT T                 ⟧T δ = SetI (⟦ T ⟧T δ)
-- -- --   ⟦ Map T₁ T₂              ⟧T δ = MapI (⟦ T₁ ⟧T δ) (⟦ T₂ ⟧T δ)
-- -- --   ⟦ ListT T                ⟧T δ = List (⟦ T ⟧T δ)
-- -- --   ⟦ MerkleTree d T         ⟧T δ = MerkleTreeI d (⟦ T ⟧T δ)
-- -- --   ⟦ HistoricMerkleTree d T ⟧T δ = HistoricMerkleTreeI d (⟦ T ⟧T δ)
