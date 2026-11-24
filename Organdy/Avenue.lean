import Organdy.Ice
import Organdy.Silent
import Organdy.Emitter
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

open Buffered Swell Oise
lemma Cymbal.friends {u v:Support (More n)}{x y:Mark n}{X Y:phy n}
 (e:Cymbal u x X a) (r:Cymbal v y Y b)
 (d:Disjoint u v) (w:Orbit n):
    Commute (X w) (Y w):=by
  have l:Disjoint (modesIn n u) (modesIn n v):=
    disjoint_left.mpr (fun i t l=> disjoint_left.mp d ((modes_at u i).mp t) ((modes_at v i).mp l))
  exact (by simpa [Sector.grainB] using (e.spare w).apart (r.spare w) l : X w * Y w=Y w * X w)

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

variable (S : I→Support (More (age P.run i s)))
/-- Schrödinger-level imprint -- every brought reading. -/
abbrev deform (R:GramM n) (E:Key I→RegBudget n)(F:Key I→ForceBudget n)(z:Key I):=
  color_b R R.beta (R.F+E z) R.slip (R.K+F z) R.v

structure Reverberate
    (o:I→Site N')
    (S : I→Support (More N')) (D:I→Mark N')(c:I→ℝ)
    (U:I→phy N') (E:Key I→RegBudget N')(F:Key I→ForceBudget N'):Prop where
  glows:∀ j:I,Cymbal (S j) (D j) (U j) (c j)
  positive:∀ j:I,0≤c j

  tip(l:List I)(b:ψS (node ∘o) l)(w:l.Pairwise fun i j=> Disjoint (S i) (S j))
    (v:Orbit N')(f:FleetS (p').threshold v.1) (e:Injective (priorP v.2)):
    Mew.tipI (fun z=> denZ (deform R✤ E F z) (Λ).U KL v) l=
       acts ((l.map U).prod v) (denZ R✤ (Λ).U KL v)

variable {S} {fees:I→ℝ}{U:I→phy (age P.run i s)} -- c:ℝ conflict, use fees
    {D:I→Mark (age P.run i s)}


variable {γ:ℝ}{M:ℕ}
variable {o:I→Site (age P.run i s)}{V:I→Bag (age P.run i s)}
   {A B:I→ Aura (age P.run i s)→ℝ} {r:Aura (age P.run i s)→Support (More (age P.run i s))→ℝ}
   (T:Tumble (RootBook P.run i k s).p P.par.h P.par.J.n (RootBook P.run i k s).K M a b γ (node ∘ o) V A B r)
local notation "τ✤" => (Classical.arbitrary _ : Ids N')
-- s' = #I+1
local notation "s₁" => (Fintype.card (Seat N')+1)
local notation "Ψ₀" => T.pow.sleigh
local notation "pσ" => T.tine.toPollen
local notation "E₀" => pend pσ
local notation "DK" => lensD (P:=p') (R✤).K (pσ).soar s₁ τ✤
local notation "DV" => lensPort (P:=p') (R✤).K (pσ).soar s₁
local notation "σ'" => (node ∘ o)


lemma wiring (V:I→Bag N')
   (r:∀ j:I,smoothRide P i k s (U j) (V j))
   (v:Orbit N')(e:Injective (priorP v.2))(z:Key I)(x:Wave (Dwell N')):
   curtain P i k s v (acts (∑ X:Aura N',trawling V z v X) x)=acts (Liss.waveΦ (fun j=> U j v) z) (curtain P i k s v x):=by
 simp only [trawling,swipe,Finset.sum_apply,Pi.smul_apply]
 rw [Finset.sum_comm]
 simp_rw [←Finset.smul_sum]
 unfold Liss.waveΦ
 nth_rw 1 [act_sum];rw [map_sum]
 conv_rhs => rw [act_sum]
 exact sum_congr rfl fun j _=>by rw [act_smul,map_smul,r j v e,act_smul]

lemma ariseGuide
 (W:I→phy N')(y:∀ j:I,0≤fees j)
 (t:∀ j:I,Cymbal (S j) (D j) (W j) (fees j))
 (u:∀ j:I,smoothRide P i k s (W j) (V j)):
    Reverberate P i k s o S D fees W
       (awake σ' DK E₀) (bustle σ' DV):=by
 have t₀:=P.par.height
 have m(j):=opening pσ j τ✤

 have β (i:I):=conducts Ψ₀ (pσ).soar σ' q' (trawling V) T.paid s₁ t₀ τ✤ i (by omega : s₁≥1) E₀ (m i) -- tune
 refine ⟨t,y,fun l δ g v hp y'=>?_⟩
 have hs: l.length ≤ s₁ :=List.length_map (as:=l) (f:=σ') ▸ δ.length_le_card.trans (Nat.le_succ _)
 have eqV: (l.map W).prod v = (l.map (fun j=> W j v)).prod:=by -- avoid induction dep
    let q:phy N' →* FC (Single N') := ⟨⟨fun x=> x v,rfl⟩,fun _ _=>rfl⟩
    exact (map_list_prod q (l.map W)).trans (by rw [List.map_map];rfl)
 rw [eqV]
 exact rackKey (Λ).U KL v Ψ₀ (pσ).soar σ' q' (trawling V) T.paid s₁ t₀ τ✤
    (projects_here P.run i k s v).1 l δ E₀ β (fun j=>W j v) hp hs (g.imp fun d=>(t _).friends (t _) d v)
    (fun z _ x=>wiring P i k s V u v y' z x)



lemma arise
    (e:∀ j:I,Echo P i k s (S j) (D j) (V j) (fees j)):
    ∃ U, Reverberate P i k s o S D fees U
       (awake σ' DK E₀) (bustle σ' DV):=by
 choose W y t u using e
 exact ⟨W,ariseGuide P i k s T W y t u⟩
structure DoubleR (p:BudgetPoint)(C:Occlus p)(M:ℕ)(f μ:ℝ):Prop where
  cash : f ≤ μ
  gate:9*2*M ≤ C.η*(p.B:ℝ)^2
  bonus:2*f*M+TreasuryFog.sigma (C.η+C.η) p.B*yσE p C ≤ μ
  coal:Real.exp (2*M)*yσF p C ≤ μ
/-- Public display for a root width L. -/
structure Wintergate (L:Side)
    (R₁ μ ν ν₁:ℝ) (o:I→Site N')
    (E:Key I→RegBudget N')(F:Key I→ForceBudget N'):Prop where
 notify: Notice o E F
 normal:∀ z:Key I,(∀ i, ‖z i‖≤2) →
    IncX primeU (E z) p' h' μ ∧ Dark primeU (F z) p' h' μ
 helix:∀ i:I,Axon L.val (o i) p' (νTip E i) h' μ 0
 port:PanoramaBill p' h' R₁ ν ν₁ E F

lemma tickets {X R₁ ν ν₁ μ:ℝ}
    (w:Force_M (p').B σ' M)
    {L:Side}
    (width:∀ i:I, Organdy.Pavilion L.val p' (V i))
    (a:PortRates Ψ₀ M X R₁ (spending p' b) ν ν₁)
    (y:DoubleR p' Ψ₀ M (spending p' b) μ):
    Wintergate P i k s L R₁ μ ν ν₁ o
       (awake σ' DK E₀) (bustle σ' DV):=by

   let α(_ :I):ArcΦ:=0
   have ht:=P.par.height
   have ax (j:I):Axon L.val (o j) p' (pend pσ j) h' (spending p' b) (α j):=
      Organdy.horn j o T.tine (le_trans (by decide:3≤10) T.width) (zero_le_one.trans ht) (width _)
   obtain ⟨n,g⟩:=displayC Ψ₀ (pσ).soar σ' q' (trawling V) T.paid s₁ ht τ✤ L o E₀ α _ rfl ax
   refine ⟨n,fun z b=>?_,fun j=>?_,buoyancy o Ψ₀ (pσ).soar q' (trawling V) T.paid s₁ ht τ✤ w a L.val E₀ α ax⟩
   · have hx:4≤Real.exp 2:=by rw [←Real.log_le_iff_le_exp (by norm_num),show (4:ℝ)= 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; have h:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num);linarith
     have h:= lentEra Ψ₀ (pσ).soar σ' q' (trawling V) T.paid s₁ ht τ✤ L o E₀ α _ rfl ax _ hx (by norm_num) y.gate w a.fee z b
     exact ⟨Provides.liftE _ R✤ _ _ h.1 y.bonus,Provides.liftQ _ R✤ _ _ h.2 y.coal⟩
   rw [(g j).1]
   exact ⟨Provides.liftE _ R✤ _ _ (ax j).vest y.cash,(ax j).site,(ax j).3⟩ -- tune
end YM.CF.Organdy
