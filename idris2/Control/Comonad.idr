module Control.Comonad 

%default total 

public export 
interface Functor w => Comonad w where 

  extract : w a -> a 

  duplicate : w a -> w (w a) 
  duplicate = extend id 

  extend : (w a -> b) -> w a -> w b 
  extend f = map f . duplicate
