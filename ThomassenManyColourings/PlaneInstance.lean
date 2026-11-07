/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneExcise

/-!
# Plane near-triangulations satisfy the interface (layer B, part 11)

`planeNTCalc` is the `NTCalc` structure whose near-triangulations are the plane
near-triangulations `PNT`: every geometric fact used by the colouring arguments is proved for
them in the files `PlaneNT` … `PlaneExcise`.
-/

@[expose] public section

namespace ThomassenManyColourings

/-- **The geometric interface, realised by plane near-triangulations.** -/
noncomputable def planeNTCalc (V : Type*) [DecidableEq V] [Fintype V] : NTCalc V where
  NT := PNT
  nodup := fun h => h.nodup
  two_le := fun h => h.two_le
  subset := fun h => h.subset
  adj_cons := fun h => h.adj_cons
  two := fun h => h.two
  rotate := fun h => h.rotate
  reverse := fun h => h.reverse
  chord := fun h h1 h2 h3 => h.chord h1 h2 h3
  delete := fun h h3 hch => h.delete h3 hch
  cut := fun h huS hu hux huy hxy => h.cut huS hu hux huy hxy
  apex2 := fun h huS hwS hu hw huw hux huy hwx hwy => h.apex2 huS hwS hu hw huw hux huy hwx hwy
  excise3 := fun h h₁ hS hint => h.excise3 h₁ hS hint

end ThomassenManyColourings
