module Basic

%prefix_record_projections off

%default total

public export
record Category where
  constructor MkCategory
  object : Type
  morphism : object -> object -> Type
  identity 
    : {a : object}
    -> morphism a a
  compose 
    : {a, b, c : object}
    -> (f : morphism a b)
    -> (g : morphism b c)
    -> morphism a c
  lawLeftIndentity
    : {a, b : object}
    -> (f : morphism a b)
    -> compose identity f = f
  lawRightIndentity
    : { a, b : object}
    -> (f : morphism a b)
    -> compose f identity = f
  lawAssociativity
    : {a, b, c, d : object}
    -> (f : morphism a b)
    -> (g : morphism b c)
    -> (h : morphism c d)
    -> compose (compose f g) h 
      = compose f (compose g h)

public export
unitCategory : Category
unitCategory = MkCategory 
  () 
  (const $ const $ ()) 
  ()
  (\()  , () => ())
  (\() =>  Refl)
  (\() =>  Refl)
  (\(), () ,() => Refl)

oppsite : Category -> Category
oppsite c = 
  MkCategory 
    c.object 
    (\a, b => c.morphism b a) 
    c.identity
    (\f, g => c.compose g f)
    c.lawRightIndentity 
    c.lawLeftIndentity
    (\f, g, h => sym $ c.lawAssociativity h g f)

public export
record Functor (cat1 : Category) (cat2 : Category) where
  constructor MkFunctor
  mapObject : cat1.object -> cat2.object
  mapMorphism
    : {a, b : cat1.object} 
    -> cat1.morphism a b 
    -> cat2.morphism (mapObject a) (mapObject b)
  lawPreserveIdentity
    : {a : cat1.object} 
    -> mapMorphism {a = a} {b = a} (cat1.identity {a = a}) 
      = cat2.identity {a = mapObject a}
  lawPreserveCompose
    : {a, b, c : cat1.object}
    -> (f : cat1.morphism a b)
    -> (g : cat1.morphism b c)
    -> mapMorphism {a=a} {b=c} (cat1.compose {a=a} {b=b} {c=c} f g)
      = cat2.compose {a=mapObject a, b=mapObject b, c=mapObject c}
        (mapMorphism {a=a} {b=b} f) (mapMorphism {a=b} {b=c} g)

public export
idFunctor : Functor cat cat
idFunctor = MkFunctor id id Refl (\f, g => Refl)

public export
composeFunctor
  : {cat1, cat2, cat3 : Category}
  -> Functor cat1 cat2
  -> Functor cat2 cat3
  -> Functor cat1 cat3
composeFunctor f1 f2 = MkFunctor
  (f2.mapObject . f1.mapObject)
  (f2.mapMorphism . f1.mapMorphism)
  -- ?help
  (trans (cong (f2.mapMorphism {a=_} {b=_}) f1.lawPreserveIdentity) f2.lawPreserveIdentity)
  (\f , g =>
    let
      l1 = cong (f2.mapMorphism {a=_} {b=_}) (f1.lawPreserveCompose f g)
      l2 = f2.lawPreserveCompose (f1.mapMorphism f) (f1.mapMorphism g) 
    in
      trans l1 l2
  )


public export
record NatrualTransformation (cat1, cat2 : Category) (f, g : Functor cat1 cat2) where
  constructor MkNatrualTransformation
  component : (a : cat1.object) -> cat2.morphism (f.mapObject a) (g.mapObject a)
  lawCommutativity 
    : {a, b : cat1.object}
    -> (t : cat1.morphism a b)
    -> cat2.compose {a=f.mapObject a, b=f.mapObject b, c=g.mapObject b} (f.mapMorphism {a=a} {b=b} t) (component b)
      = cat2.compose {a=f.mapObject a, b=g.mapObject a, c=g.mapObject b} (component a) (g.mapMorphism {a=a} {b=b} t)

public export
idNatrualTransformation : (cat1, cat2 : Category) -> (f : Functor cat1 cat2) -> NatrualTransformation cat1 cat2 f f
idNatrualTransformation cat1 cat2 f = MkNatrualTransformation
  (\a => cat2.identity {a= f.mapObject a})
  (\t  => 
    let 
      l1 = cat2.lawLeftIndentity (f.mapMorphism t)
      l2 = cat2.lawRightIndentity (f.mapMorphism t)
    in trans l2 (sym l1)
  )
