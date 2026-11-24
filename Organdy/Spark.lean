import Organdy.Entry
import Organdy.Melt
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Vale Buffered Roots Tulip QuadClock Neon

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
variable (P:Spine) (i k s:ℕ)
local notation "Λ"=>P.par
local notation "x'"=> Vale.hat (Λ).R.L (Λ).x s
local notation "N'"=> age P.run i s
local notation "KL"=> (P.run.voyage i).CapeT s
local notation "R✤"=>RootBook P.run i k s
local notation "p'" => (R✤).p
local notation "q'" => (Λ).J.n
local notation "h'" => (Λ).h

open Swell Pressure Py.Rate.BScale Yoke MeasureTheory
open Buffered.Afterglow
local notation "κ'" => Journey.compass P.run i k s
local notation "O" => coined P.run i k s
variable {M:ℕ}{L:Side}{μ W:ℝ}
variable {o:I→Site (age P.run i s)}
    {S:I→Support (More (age P.run i s))}
    {D:I→ Mark (age P.run i s)}{fee:I→ℝ}
    {U:I→phy (age P.run i s)}
    {E:Key I→RegBudget (age P.run i s)}
    {F:Key I→ForceBudget (age P.run i s)}

lemma caustic {c:ℝ}
   (e:Reverberate P i k s o S D fee U E F)
   (g:Wintergate P i k s L W μ μ 1 o E F)
   (v:2≤W)
   (Z:ShelterCost c P.run s i k)
   (b:μ ≤ slotFee (Λ) s)
   (h:(P.run.voyage i).kick ≤k)
   (l:List I) (q:ψS (node ∘o) l)
   (t:l.Pairwise fun j k=>Disjoint (S j) (S k)):
   let d:=(l.map D).prod
   let u:=artwork P.run i k E F l
   let f:= fun x=>beamZ N' (u x)
   let A:ℝ:=1/2
   Integrable f (city N') ∧ O ≠0 ∧ (∫ x,f x ∂ city N')/O = κ' d
     ∧ ‖κ' d‖ ≤ laserRent (Λ) (2 / W) A s N' (Fintype.card I) l.length:=by

   intro d u f t₁
   have hp:= parade l (fun j _=> e.glows j) t (fun j _=>e.positive j)
   let j:=fun x:Orbit N'=>letterRead (d (x.1,KL x)) (denZ R✤ (Λ).U KL x)
   have a: ∀ᵐ x ∂ city N', FleetS (p').threshold x.1:=by
     have hu:p'=P.run.meter.a s:=(Papal.prices_plot P.run s i k Z.load.paid).1
     rw [hu]; exact ae_fleet (((P.run.voyage i).paths k).paid.can.isle s) -- defeq? tune
   have he:j=ᵐ[city N'] f:=by
     filter_upwards [a,Window.priorTag (N:=N')] with x L G
     exact (play hp KL x _).trans (congrArg (beamZ _) (e.tip l q t x L G).symm)
   obtain ⟨m,n,y⟩:= Tapestry.funds P.run s i k hp.realc.env h Z.load.paid
   have ux:Integrable f (city N'):= m.congr he
   have r: (∫ x, f x ∂ city N')/O=κ' d:=
      (congrArg (· / O) (integral_congr_ae he).symm).trans y.symm
   refine ⟨ux,n,r,?_⟩
   rw [←r]
   have w:0<W:=by linarith
   have p:0 < 2/W:=by positivity
   have ρ:2*(2/W)⁻¹=W:= by field_simp
   have b': PanoramaBill p' h' (2*(2/W)⁻¹) μ (2*t₁) E F:=by
       rw [ρ,show 2*t₁=1 from by unfold t₁;ring]
       exact g.port
   exact glassPrice P.run Z E F p ((div_le_one w).mpr v)
      (b.trans Z.load.health.2.2.2.1) b' o g.notify l ux


variable {Ψ Φ:ℝ→ℝ}
/-- Sold for all activated periods using actual denominator. -/
def SignedLease (P:Spine)(M:ℕ)(L:Side)(J G Ψ Φ:ℝ→ℝ)(w:ℕ):Prop :=
   leased P M L J G Ψ Φ w ∧
   ∃ α, ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<P.run.uv k →
    let y:=hat P.par.R.L P.par.x s
    let r:=RootBook P.run i k s
    Φ y ≤ slotFee P.par s ∧
    ((P.run.voyage i).kick ≤ k → ShelterCost α P.run s i k) ∧
    (r.p.B=radiusB y → r.p.order=6 → r.p.power=2 →
      r.p.supportExponent=1 →
      Kyanite P i k s M L (J y) (G y) (Ψ y) (Φ y) (prismPan P.par.R w y))
lemma signed {J G:ℝ→ℝ}{w Mc:ℕ}(e:Stakes Mc P)
    (v:leased P M L J G Ψ Φ w):
    SignedLease P M L J G Ψ Φ w:=by
  obtain ⟨α,_,_,Z,_⟩:=e.pressure
  refine ⟨v,α,?_⟩
  filter_upwards [v.2.2.2.2,Z,(turnover P.par).eventually
     (bound_w P.par.R 0 Φ v.2.2.2.1), (turnover P.par).eventually (opulence P.par.R w M)] with s t z y u

  let x:=hat P.par.R.L P.par.x s
  have he :0<slotFee P.par s:=u.1
  have hx: Φ x ≤ slotFee P.par s:= by
    change (((1+(radiusB x:ℝ))^0*(slotFee P.par s)⁻¹)*Φ x)≤1 at y
    rw [pow_zero,one_mul,inv_mul_le_iff₀ he,mul_one] at y; exact y
  filter_upwards [t,z] with i a b k r
  exact ⟨hx,fun hk=>b k hk r.le, a k r⟩
end YM.CF.Organdy
