import Organdy.Coupon
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

open Swell Pressure Py.Rate.BScale

structure Kyanite (P:Spine)(i k s:ℕ)(M:ℕ)(L:Side)
    (a b γ μ W:ℝ):Prop where
   launch:Polar (RootBook P.run i k s).p P.par.h P.par.J.n (RootBook P.run i k s).K M L.val a b γ
   pressed:∃ α,PortRates launch.stalls.sleigh M α W (spending (RootBook P.run i k s).p (outfit L.val b)) μ 1
   house:DoubleR (RootBook P.run i k s).p launch.stalls.sleigh M (spending (RootBook P.run i k s).p (outfit L.val b)) μ
   cost:0≤μ
   width:2≤ W

lemma sunny (B:ℕ) (v:I→Seat n){M:ℕ} (w:Force_M B v M): breeze v M :=by
  intro x
  refine (card_le_card ?_).trans (w.2 x)
  intro j p
  refine mem_filter.mpr ⟨mem_univ _,?_⟩; rw [(mem_filter.mp p).2,separation_self]
  omega


variable {M:ℕ}{L:Side}{γ μ W:ℝ}
variable {F G Ψ Φ:ℝ→ℝ}
variable {o:I→Site (age P.run i s)}
    {S:I→Support (More (age P.run i s))}
    {D:I→ Mark (age P.run i s)}{C:I→ℝ}
    {V:I→Bag (age P.run i s)}

lemma Kyanite.melts (j:Kyanite P i k s M L a b γ μ W)
    (w:Force_M (p').B (node ∘o) M) (v:∀ x:I,Spring P i k s (o x) (S x) (D x) (V x) (C x) a b):
    ∃ U E F, Reverberate P i k s o S D C U E F ∧
       Wintergate P i k s L W μ μ 1 o E F:=by
  obtain ⟨y,n,A,B,r,T⟩:=playSpring P i k s j.launch (sunny _ _ w) v
  obtain ⟨α,u⟩:=j.pressed
  obtain ⟨U,z⟩:= arise P i k s T y
  exact ⟨U,_,_,z,tickets P i k s T w n u j.house⟩

/-- for any post-appointments. -/
def leased (P:Spine)(M:ℕ)(L:Side)(F G Ψ Φ:ℝ→ℝ)(w:ℕ):Prop :=
  Chill_v F ∧ Quench P.par.R G ∧ Quench P.par.R Ψ ∧ Quench P.par.R Φ ∧
  ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<P.run.uv k →
    let y:=hat P.par.R.L P.par.x s
    let r:=RootBook P.run i k s
    r.p.B=radiusB y → r.p.order=6 → r.p.power=2 →
     r.p.supportExponent=1 →
     Kyanite P i k s M L (F y) (G y) (Ψ y) (Φ y) (prismPan P.par.R w y)

lemma all_wages {M:ℕ}(H:P.FirstLease) (L:Side) (w:ℕ)
   (d: Chill_v F)(e:Quench P.par.R G):
   ∃ Ψ Φ,leased P M L F G Ψ Φ w:=by
 let R:=P.par.R
 obtain ⟨Γ,u,v,ζ,b⟩:=coldPays P H M L.val d e
 let X(y):=outfit L.val (G y)
 let Z:=bankFee X Γ M
 have χ:Quench P.par.R Z:=chills _ _ _ _ (e.normF.manyF _) ζ
 refine ⟨Γ,Z,u,v,ζ,χ,?_⟩
 let t:=turnover P.par
 have l:=opulence R w M
 filter_upwards [b,t.eventually (bound_w R w Z χ), t.eventually l, (Work.E01.radiusB_tendsto.comp t).eventually_ge_atTop (18*M)] with s₀ y z x p
 filter_upwards [y] with i₀ f k₀ g

 intro h r hB hQ hP hO
 let S:=f k₀ g hB hO
 have hp:hoard r.p=Nor.reserveT 2 6 (radiusB h) (runway h):=by
    unfold hoard biscuit; rw [hP,hQ,hB];rfl
 have hh:gather M (hoard r.p) (X h) (Γ h)=Z h:=by
    rw [hp];rfl
 obtain ⟨d',e'⟩ := imprest S.stalls (outfit_zero _) (show 1≤prismPan R w h from one_le_two.trans x.2.1)
    (by rw [hB];exact x.2.2) (by rw [hB];exact p) (by rw [hh];exact z)
 rw [hh] at d' e'
 exact ⟨S,⟨_,d'⟩,e',d'.fee.trans e'.cash,x.2.1⟩
end YM.CF.Organdy
