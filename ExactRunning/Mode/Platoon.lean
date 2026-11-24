import ExactRunning.Mode.Booth
/-! # Root vertical tangents — flat frame -/

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

lemma stable_zero :
    X.Stable (m:=m) 1 1 := by
  let F : Point G m (X.up m)→ℝ := fun z=> X.J m (X.V0 z) (X.B0 z)
  have hs : ContDiffAt ℝ ω F 0 := Thaw.earn X.branches _ X.B0_lit X.B0_fine X.V0_lit E.paths
  have he : fderiv ℝ F 0=0 := triple_star X.simple
    (fun u=>Filter.Eventually.of_forall fun z=>by
      change X.J m (X.V0 _) (X.B0 _)=_
      rw [V0_star,B0_star]
      exact root_wages _ (X.choice m) X.branches _ _ _ E.p E.r E.paths _)
    (hs.differentiableAt (by simp))
  let R := ContinuousLinearMap.inr ℝ (Link G m) (Vault G m (X.up m))
  have f : ContDiffAt ℝ ω F (R 0) := by rw [map_zero];exact hs
  have hf : canon (X.S m) (X.choice m) E.p E.r 1 1 = F ∘ R := by
    funext y
    change X.J _ _ (_*1)= X.J _ (input _ _ 0) _
    rw [input_zero,mul_one];rfl
  unfold Stable Shell;rw [hf]
  refine ⟨f.comp _ R.contDiff.contDiffAt,?_⟩
  rw [fderiv_comp _ (f.differentiableAt (by simp)) R.differentiableAt,map_zero,he];rfl

variable {α β : Type} [Fintype β] [DecidableEq β]

def zap (f : α → β) (R : Type) [Zero R] [One R] : Matrix α β R :=
  (1:Matrix β β R).submatrix f id

lemma zap_apply {R:Type} [NonAssocSemiring R] (f : α → β) (x : β → R) :
    zap f R *ᵥ x = x ∘ f := by funext i; simp [zap,mulVec,dotProduct, one_apply]

def root (m : Side) (b : Lines G m 0) : Lines G (X.up m) 0 :=
  ((X.S m).ratio.embed b.1,b.2)

lemma stamps (a : Lines G m 0) :
    X.Fid.pack m (X.root m a) = (a.1,0,a.2) := by
  apply (X.Fid.pack m).symm.injective
  rw [(X.Fid.pack m).symm_apply_apply]
  refine Prod.ext ?_ rfl
  change (X.S m).ratio.embed a.1=(X.S m).ratio.embed a.1 + wrap _ (lift (0:Site _))
  simp [show lift (n:=(X.S m).ratio.count) 0=0 by ext; simp [lift]]

lemma flat_rear : stood (X.S m) (G:=G) 1 = fromRows (mail 1) (-zap (X.root m) ℝ) := by
  apply Matrix.ext_of_mulVec_single
  intro i
  simp only [stands,fromRows_mulVec,mailed,neg_mulVec,zap_apply, helmets, halvesC,cash_pocket]

  let v : BaseSites G (X.up m) := Pi.single i (1:ℝ)
  have h := soldier_mounted (X.S m) 1 v
  refine congr_arg₂ Sum.elim h.1 ?_
  funext j
  have hp : j.2.1=vac := vac_only _
  have ht := h.2 j.1
  simp only [Prod.snd_one,Pi.one_apply,G.adjoint_one] at ht

  rcases j with ⟨j,a,b⟩; change a=vac at hp; subst a
  exact congr_arg (fun z:G.Color => z b) ht

def catcher :
    Tray G (Loom G) X.Fid (fun m _=> zap (X.root m) ℝ) :=
  Tub.stock (Du G) (Loom G) X.Fid _ (fun _=> zap (fun i=>(0,i)) ℂ)
    ⟨1,zero_lt_one,Poster.web _⟩ <| by
      intro m a _ _ x
      rw [add_zero,zap_apply]
      let P := X.Fid.pack m
      change repackM (Equiv.refl _) P (approached (zap _ ℝ)) *ᵥ tune _ _=_
      let q := tune a x
      rw [show approached (zap (X.root m) ℝ) = zap (X.root m) ℂ by
        ext i j; simp [approached,zap,one_apply,apply_ite]]
      rw [show tune a x=(q ∘ P) ∘ P.symm by ext; simp [q], repack_act,zap_apply]
      ext i
      simp only [Function.comp_apply, Equiv.refl_symm,Equiv.refl_apply, P,X.stamps]
      rfl

def platoon :
    Tray G X.Barrel X.Fid (fun m _=> stood (X.S m) (G:=G) 1) :=
  (X.fineMail.freeze.rows X.catcher.negate).shift <| by
    intro m
    simp_rw [X.flat_rear,X.fg_bg_zero]
    rfl

end BlockTie
end ExactRunning
