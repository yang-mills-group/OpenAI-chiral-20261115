import ExactRunning.Mode.Manner
/-!
# Assembly on top of the classical joint Hessian

Off-shell background family uses two independent coarse inputs, for coarse links
and for the lift via chevron (fine input and fedora frame).
`glows` and `pulse` give the two completed Hessians (full and high),
`railings` transfers intertwinings to set up finite cut calculations.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024
namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}

open Pairing
variable (X)

def rudder :
    Tray G X.Fid X.Barrel (fun m z=> X.settings (X.fg_bg m z)) :=
  (X.fineMail.tr.mul (Tub.fst _ _ _)).shift <| by
    intro m; simp_rw [settings, X.rear_place];rfl

def glows :
    Tray G X.Hold X.Hold
      (fun m z => X.vibrant (X.fg_bg m z) (co_bg G m z)) :=
  X.perfect.plus (.blocks (X.rudder.tr.mul X.rudder) (.nil ..) (.nil ..)
    ((belle G).mul (belle G).tr))

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {R : Type} [Semiring R]

lemma topLeft_eq (M : Matrix (α ⊕ β) (α ⊕ β) R) :
    πl _ _ R * M * (πl _ _ R)ᵀ = M.toBlocks₁₁ := by

  ext i j
  simp [πl, Matrix.mul_apply,Fintype.sum_sum_type, Matrix.one_apply];rfl

def cogWheel : Tray G X.Barrel X.Barrel
      (fun m z => X.thick (X.fg_bg m z) (co_bg G m z)) :=
  let l := Tub.fst (Du G) X.Barrel (Front G)
  ((l.mul X.perfect).mul l.tr).shift <| by
    intro m
    filter_upwards [X.full_fare (X.fg_bg_lit m) (by simp) (co_bg_lit (G:=G) m)] with z hz
    rw [topLeft_eq]
    exact X.full_up hz

def pulse : Tray G X.Barrel X.Barrel
      (fun m z => X.high (X.fg_bg m z) (co_bg G m z)) :=
  X.cogWheel.plus (X.clears.tr.mul X.clears)

def outerGhost (G : Gauge) : Tray G (Loom G) (Loom G) (fun m z => tonic (co_bg G m z)) :=
  (belle G).tr.mul (belle G)

def innerGhost :
    Tray G X.Fid X.Fid (fun m z => tonic (X.fg_bg m z).1) :=
  X.fineMail.tr.mul X.fineMail

def fas :
    Tray G X.Scroll X.Scroll (fun m z => epMat E.p E.r (X.fg_bg m z).1) :=
  X.sweet.plus (X.fineMail.mul X.fineMail.tr)


lemma rail' (r m) {u : ℝ → Box G m} (i : u 0=0) (j : DifferentiableAt ℝ u 0)
    (k : (ridge r).repeats (deriv u 0)) :
    X.Rail r (X.fg_bg m ∘ u) (co_bg G m ∘ u) :=
  ⟨X.perfect.fit (X.hold_cut r m) (X.hold_cut r m) i j k,
    (belle G).fit (.refl _) (.refl _) i j k,
    X.fineMail.fit (X.rolled_cut r m 1) (X.rolled_cut r m 0) i j k,
    X.clears.fit (X.rolled_cut r m 0) (X.barrel_cut r m) i j k,
    X.blow.fit (X.rolled_cut r m 0) (X.rolled_cut r m 0) i j k⟩

lemma railings (r m) : X.Railings r m := by
  intro x z h he hd hg
  let C := strap G m
  let u (t:ℝ) := C (z t,t • x)
  have i : u 0=0 := by unfold u; rw [he,zero_smul]; exact map_zero C
  have D : HasDerivAt u (C (deriv z 0,x)) 0 := by
    apply C.hasFDerivAt.comp_hasDerivAt
    have e : HasDerivAt (fun (t:ℝ) => t • x) x 0 := by
      simpa using (hasDerivAt_id' (0:ℝ)).smul_const x
    exact hd.hasDerivAt.prodMk e
  have j := D.differentiableAt
  have k : (ridge r).repeats (deriv u 0) := D.deriv.symm ▸ tie_repeats hg h
  have f := X.rail' r m i j k
  rw [show X.fg_bg m ∘ u=(fun t => X.lead m (t•x)) from
     funext fun t => congr_arg (X.lead m) (show inner G m (u t) = _ from rfl)] at f
  exact f


end BlockTie
end ExactRunning
