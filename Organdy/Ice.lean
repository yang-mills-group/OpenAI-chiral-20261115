import Organdy.Boreal
import Organdy.Acrid
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


open Vale Buffered Py.Rate.BScale

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

lemma immense (P:Spine) (s:ℕ):
    Tendsto (fun i=> (More (age P.run i s)).val) atTop atTop:=by
  refine tendsto_atTop_mono ?_ (show Tendsto (fun i=>(age P.run i s).val) atTop atTop from
    tendsto_atTop_mono (fun i=> Vale.amplit ..) P.run.ir_grows.tendsto_atTop)
  intro i; change _ ≤ _ * 2;exact Nat.le_mul_of_pos_right _ (by decide)

/-- Parametric *after* M8 on the same P. buoys downstream: any launches with
C full and G birth costs. -/
abbrev Freezer (P:Spine)(M L:ℕ)
    (C G Γ:ℝ→ℝ):Prop :=
   Chill_v C ∧ Quench P.par.R G ∧ Quench P.par.R Γ ∧
   ∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ k:ℕ,s<P.run.uv k →
     let R:=RootBook P.run i k s
     let y:=hat P.par.R.L P.par.x s
     R.p.B=Pressure.radiusB y →
     R.p.supportExponent=1 →
     Polar R.p P.par.h P.par.J.n R.K M L (C y) (G y) (Γ y)

lemma coldPays (t:P.FirstLease) (M L:ℕ)
    {C G:ℝ→ℝ} (v:Chill_v C)(g:Quench (Λ).R G):
    ∃ Γ,Freezer P M L C G Γ:=by
    obtain ⟨Z,W,V1,U,pℓ,q⟩ :=(warmLease t).dust
    obtain ⟨Γ,α,β⟩:=buySleigh (Λ).R _ _ U
       (shortCoat _ M L v) (Eventually.of_forall (properWinter C M L))
       pℓ.mint (longCoat (Λ).R G M L g)
    refine ⟨Γ,v,g,α,?_⟩

    filter_upwards [(turnover P.par).eventually β, q,
      (Work.E01.radiusB_tendsto.comp (turnover P.par)).eventually_ge_atTop 10] with s₀ y h r
    let x:=hat P.par.R.L P.par.x s₀
    filter_upwards [(immense P s₀).eventually_ge_atTop (2*(massif L*Pressure.radiusB x))] with i₀ w k₀ hk
    intro R y₁ B S
    obtain ⟨z,a⟩:=y R.p B
    refine ⟨by rw [B];exact w, by rw [B]; exact r,S,P.par.height,?_,_,z,dusty (h i₀ k₀ hk)⟩
    unfold Stalls capstan
    rw [B]
    exact a

open Swell
variable (j:Site (age P.run i s))
def smoothRide (U:phy N')(V: Sour.Bag N'):Prop:=
 ∀ z:Orbit N',Injective (priorP z.2)→∀ x:Wave (Dwell N'),curtain P i k s z (acts (∑ u:Aura N', V u z) x)=
    acts (U z) (curtain P i k s z x)

/-- Single-root tint. No normalization fixed here (for use on e.g. Y° scaled).
Support S of mark distinct from the supports of the launches. -/
structure Spring (S:Support (More N'))
    (D:Mark N')(V:Sour.Bag N')(c a b:ℝ):Prop where
    smooth: ∃ U:phy N', Cymbal S D U c ∧ smoothRide P i k s U V
    plus: 0≤c
    fare: Barrage p' q' {node j} h' V (highLaunch p') a b
-- anchored Barrage weakening requires lemma. could replace with ∃support

lemma joinsRoot -- remove Y
    {o:Seat n} {r:ℝ} {V:Bag n} {S:Support (More n)}
    (e:o∈ S)(x:Barrage p q S h V r a b):
    Barrage p q {o} h V r a b:=by
    obtain ⟨A,B,f,g,k,l⟩:=x.price
    exact ⟨A,B,f,fun X t=>g X fun m=>t (singleton_subset_iff.mpr (m e)), k,l⟩

variable {m M L:ℕ} {f g:ℝ→ℝ}
local notation "ℓ"=> (Λ).R.L
abbrev scaledBirth (P:Spine)(g:ℝ→ℝ)(y:ℝ):=g y * Py.pinpr P.par.R.L y

lemma coralSpring {J T:Axis→SOp N'}{X Y:SOp N'}{V:Sour.Bag N'}
    (z:0<=hueW ℓ x') (r:0≤b) (t:(p').supportExponent=1)
    (v:Squid P i k s m j a b f g J T X Y V) : -- s reused
    Spring P i k s j (Porch p' j) (Coral ℓ x' KL p' j J X m) V (hueW ℓ x' * yInvoice b)
    (f x') (scaledBirth P g x'):=by
    refine ⟨⟨_,v.appointment,fun z _ x=>v.flight.science ..⟩,
      mul_nonneg z (by unfold yInvoice YcomCost; positivity),?_⟩
    rw [show highLaunch p'=rScale p' by unfold highLaunch rScale biscuit;rw [t,div_eq_mul_inv]]
    exact joinsRoot (S:=grooveB 24 p' (node j)) (halo_subset _ _ (mem_singleton_self _)) v.flight.pouch -- tune

lemma coralCold {a' b' D δ:ℝ}{w:ℕ}
    (t:P.FirstLease)
    (v:Pearling P m a b a' b' D δ w f g) (M L:ℕ):
    ∃ Γ,Freezer P M L f (scaledBirth P g) Γ:=
   coldPays P t _ _ v.cold.vanish (Qcost P.par.R g v.down)

/-- for pricing after incline. -/
def Echo (P:Spine)(i k s:ℕ)
    (T:Support (More (age P.run i s))) (D:Mark (age P.run i s))
    (V:Sour.Bag (age P.run i s))(c:ℝ):Prop:=
 ∃ U:phy (age P.run i s), 0≤c ∧ Cymbal T D U c ∧ smoothRide P i k s U V

lemma playSpring
  {u:ℝ}
  {o:I→Site N'}
  {S:I→Support (More N')}{D:I→Mark N'}{C:I→ℝ}{V:I→ Sour.Bag N'}
  (l:Polar p' h' q' (R✤).K M L a b u)
  (e:breeze (node ∘o) M)
  (v:∀ x:I, Spring P i k s (o x) (S x) (D x) (V x) (C x) a b):
  let Y:=incline (node ∘o) L p' V
  (∀ x:I,Echo P i k s (S x) (D x) (Y x) (C x)) ∧
    (∀ x:I,Pavilion L p' (Y x)) ∧
    ∃ A B r,Tumble p' h' q' (R✤).K M (outfit L a) (outfit L b) u (node ∘ o) Y A B r:=by

  intro Y
  refine ⟨fun x=>?_,l.realize V e (Y:=fun x=>{node (o x)}) (fun _=>mem_singleton_self _) (fun x=>(v x).fare)⟩
  obtain ⟨U,f,q⟩:= (v x).smooth
  refine ⟨U,(v x).plus,f,fun z e w=>?_⟩
  have h : ∑ y:Aura N',Y x y z = ∑ y:Aura N',V x y z:=by
     rw [←Finset.sum_apply,←Finset.sum_apply]
     exact congrFun (giveExpand ..) _
  rw [h]; exact q z e w
end YM.CF.Organdy
