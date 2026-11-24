import Gingham.Ruff.Salute
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

open Pike Shells
open Forge Vow
variable {a c e ρ b:ℝ} (X:Rialto 6 e ρ b)
    {A:Fob N e}
   {y:Site N}{u:Side}
variable (B:Plastron y u e (a/4) c A)
variable {l r:ℕ}{E:ℝ}{p: BudgetPoint}
  (G:Tagbill a E u l r p.B)
  (P: WharfCost a ρ p)
variable {Z:Scree.Loom N} (F:Briefly p r e Z)

def refrain (ρ:ℝ)(u:Side)(a c:ℝ):ℝ:=devour ρ u a c + c
abbrev cutoff (p:BudgetPoint):=tenderb p.B

/-- The quadratic used everywhere is the Taylor coefficient of order two in
  coordinates Dab. The affine bound is independent of torus overhead (and
  needs no mask assumption in writing the jets). -/
def musicA(p:BudgetPoint):Doub N→ℂ:= hum X (B.light (cutoff p))

structure Arioso (X:Rialto 6 e ρ b)(B:Plastron y u e (a/4) c A)
    (F:Briefly p r e Z) : Prop where
   value(x:Orbit N):
       ‖Matrix.trace (coinF F B true x)‖ ≤ refrain ρ u a c*p.threshold^2


   charges(x:Orbit N)(D Z':Support (More N))(Y:Aura N)
     (s:hoop y p.B⊆Y.val)(v:x.1∈σX p Y D):
      Allows 6 (fun i=> Matrix.trace (coinF F B true (pressQ p Z' x.1 i,x.2))) 0
          (refrain ρ u a c*p.threshold^2)
   gallery:Gallery 6 (musicA X B p) c
   linear:fderiv ℝ (musicA X B p) 0=0
   emerges(o:Doub N→ Skye.Ids N):
       (fun v=> Matrix.trace (coinF F B true (pencil ρ v,o v)))
        =ᶠ[𝓝 0] (musicA X B p)
   hearsmall {w:Doub N}(o:‖w‖<1)
    (x: Orbit N)(v: pingS p.threshold (hoop y p.B) x.1)
    (g:Seat N → SU.E) 
    (d:Agrees (belle y p.B) (pencil ρ w) (Lattice.gauge g x.1)):
       let f:=musicA X B p
       ‖Matrix.trace (coinF F B true x)-f 0-quadraticChi f w‖≤c*‖w‖^3
   fixed : ‖musicA X B p 0‖≤ fairy a p.B*c
   press : fairy a p.B ≤ p.threshold^3
   growth(w:Doub N)(t:ℝ)(g:sprays (bouton y) w t):
          Hem w t a c u (cutoff p) (hum X A) (musicA X B p)


include G P
theorem recitativo (q:2*(p.B/10+1)<(More N).val)(h:hum X A 0=0):
   Arioso X B F :=by
 have t:0≤a/4:=(div_pos G.apos (by norm_num)).le
 have j:3≤6:= by decide
 have i:(2:ℕ)≤6:=by decide
 have b:devour ρ u a c*p.threshold^2+fairy a p.B*c≤refrain ρ u a c*p.threshold^2:=by
   rw [refrain,add_mul, mul_comm c]
   exact add_le_add le_rfl (mul_le_mul_of_nonneg_right P.2.2 (carrot_c B))
 have l:0≤a/8:=(div_pos G.apos (by norm_num)).le
 let H:=B.lightP (cutoff p)
 refine ⟨fun x=>(flashfee X B G P.1 F q i h x).trans b,
    fun x D Z' Y v t=>(basque X B G P.1 F q i h x D Z' Y v t).mono b, 
    by simpa only [musicA,one_mul] using sing X H t, sing_flat X H t (by decide),
    pulse X B G F, hearsmall X B G F j,?_,P.2.1,
    fun _ _ v=> bobbin X B _ G.apos j v⟩
 let B₂:= B.flightP (cutoff p) (show a/8≤a/4 from by linarith)
 unfold musicA hum at *
 rw [B.split_m (cutoff p) _,Matrix.trace_add,add_eq_zero_iff_eq_neg] at h
 rw [h, norm_neg]
 exact ((sing X B₂ l) 0 (by simp)).value.trans (fairy_rich B G)

