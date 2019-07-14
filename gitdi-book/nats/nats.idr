data MyNat = Zero | Succ MyNat

total mynat_plus : MyNat -> MyNat -> MyNat
mynat_plus Zero m = m
mynat_plus (Succ k) m = Succ (mynat_plus k m)

-- proving that 0 + a = a
total first_proof : (a: MyNat) -> mynat_plus Zero a = a
first_proof a = Refl

-- proving that there exists an x such that Succ x exists
-- we are basically constructing a dependent pair of (x, Succ x)
-- that is accomplished with the DPair type
total second_proof : MyNat -> DPair MyNat (\_ => MyNat)
second_proof x = MkDPair x (Succ x)

data MyLTE : MyNat -> MyNat -> Type where
  MyLTEZero : MyLTE Zero right
  MyLTESucc : MyLTE left right -> MyLTE (Succ left) (Succ right)

-- proving that a + 0 = a
-- using induction here
-- what we do it rewrite the induction hypothesis
total third_proof : (a: MyNat) -> mynat_plus a Zero = a
third_proof Zero = Refl
third_proof (Succ x) = rewrite (third_proof x) in Refl
