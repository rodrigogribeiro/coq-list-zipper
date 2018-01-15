List zippers in Coq
======================

A formalization of list zippers in Coq. 
This is a formalization of the Haskell library ListZipper
available [here](http://hackage.haskell.org/package/ListZipper).

About the development
--------------------------

We use QuickChick to test the relevant properties and, after getting
the right definitions (some code in the original Haskell library wasn't accepted 
by Coq due to totality restrictions), we prove all properties.
