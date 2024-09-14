record Category where
    constructor MkCategory
    obj           : Type
    mor           : obj -> obj -> Type
    identity      : (a : obj) -> mor a a
    compose       : (a, b, c : obj)
                 -> (f : mor a b)
                 -> (g : mor b c)
                 -> mor a c
    leftIdentity  : (a, b : obj)
                 -> (f : mor a b)
                 -> compose a a b (identity a) f = f
    rightIdentity : (a, b : obj)
                 -> (f : mor a b)
                 -> compose a b b f (identity b) = f
    associativity : (a, b, c, d : obj)
                 -> (f : mor a b)
                 -> (g : mor b c)
                 -> (h : mor c d)
                 -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h


---------------------------- make discrete category

DiscreteMorphism : (x, y : a) -> Type
DiscreteMorphism x y = (x = y)



discreteIdentity : (x : a) -> DiscreteMorphism x x
discreteIdentity _ = Refl
-- idris --total
discreteCompose : (x, y, z : a) -> DiscreteMorphism x y -> DiscreteMorphism y z -> DiscreteMorphism x z
discreteCompose _ _ _ Refl Refl = Refl

discreteLeftIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x x y (discreteIdentity x) f = f
discreteLeftIdentity _ _ Refl = Refl

discreteRightIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x y y f (discreteIdentity y) = f
discreteRightIdentity _ _ Refl = Refl

discreteAssociativity : (w, x, y, z : a)
                     -> (f : DiscreteMorphism w x)
                     -> (g : DiscreteMorphism x y)
                     -> (h : DiscreteMorphism y z)
                     -> discreteCompose w x z f (discreteCompose x y z g h)
                      = discreteCompose w y z (discreteCompose w x y f g) h
discreteAssociativity _ _ _ _ Refl Refl Refl = Refl

discreteCategory : (a : Type) -> Category
discreteCategory a = MkCategory
  a
  DiscreteMorphism
  discreteIdentity
  discreteCompose
  discreteLeftIdentity
  discreteRightIdentity
  discreteAssociativity

data MyBool = MyTrue | MyFalse 

MyFirstCategory : Category
MyFirstCategory = discreteCategory MyBool

EndomorphismsOfTrue : Type
EndomorphismsOfTrue = mor MyFirstCategory MyTrue MyTrue

MyFirstArrow : EndomorphismsOfTrue
MyFirstArrow = Refl
