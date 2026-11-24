import Anomaly.Basis.Litmus
/-! Pure onsite registration to accelerator inputs (130+last paragraph of XXI).
No Loom at this operator. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill Buffered StressExchange Reed
variable {N B M:Side}{Y:SOp N}{S:Sa N}{P:BudgetPoint}{a t d f h p' x₀ y s:ℝ}{k p q j L:ℕ}
variable {K:Scree.Loom N}{o:Site N}{A:Op (Single N)} (H: Moto.Fit o P.power 1 f A)(T:DockPulse P K t d a h s j q)(l:16+1+10+q≤ j*P.B)(h₁:d≤ 1)
local notation "Ω"=>Single N
abbrev OnSite(o:Site N)(A:Op (Single N)):= ∀ i j:Single N,A i j≠0→ i.1.1=o ∧ j.1.1=o
variable (V:OnSite o A)
include V
lemma on_tuck : Tucked o A:=fun i j p=> Or.inl (congrArg Cube.node (V i j p).1.symm)
lemma runBy (x:Pane N): ρlens A (profile x)=A:=by
 ext ⟨i,u⟩ ⟨j,v⟩; rw [stride_X A i j (profile x) (fun _=>0)]
 let J:=boxM A i j; change _=J u v
 by_cases t:J=0; · unfold Swell.arm; rw [show boxM A i j=0 from t,t,zero_mul]
 obtain ⟨s,r,w⟩:∃ s r:SU.Slot, J s r≠0:=by by_contra! w; exact t (Matrix.ext fun k l=>w k l)
 have hp:=V (i,s) (j,r) w
 have hx:i.1=j.1:= hp.1.trans hp.2.symm
 have hy: Λrod i j=[]:= List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (by have h:=Font.short (node i.1) (node j.1); unfold Λrod; rw [hx]; simpa using Font.short (node j.1) (node j.1))) -- tune
 unfold Swell.arm; rw [show Font.shiftH _ _=[] from hy]; simp only [track_pr, Tulip.brand, travel]; simp; rfl -- tune
abbrev onsiteOne (A:Op (Single N)): Mark N:= fun _=> preJ (tickA N) A
local notation "Px"=> νt a d 16*(Haro.horn*f)
local notation "S_"=> offsetMask (j*P.B+12) o
include H T l h₁
lemma paidDark : WindowTag (onsiteOne A) o (j*P.B+12) (Px+Px) ∧ Contact K S_ (onsiteOne A) (firePlate K (ρlens A)):=by
 let G:=on_tuck V; let M:=measureχ H G T l h₁; let J: Orbit N := (1,Classical.arbitrary _)
 let D:=halo (j*P.B) {node o}
 have h(x:Fields N)(t:x.1∈{U:Pane N|pingS P.threshold D U}): Ωmask j P o A x= onsiteOne A x:=by unfold Ωmask χmask; rw [Set.indicator_of_mem t,runBy V x.1]
 let X:Fields N:= (J.1,1); have hx:J.1∈ {U:Pane N|pingS P.threshold D U}:=ping_f P _
 let Z:= onsiteOne A
 let Vx:=keepPH H G T l h₁
 let U:=firePlate K (ρlens A); have he(i:Orbit N): (houseK P D U) J=U i:=by unfold houseK; rw [Set.indicator_of_mem (show J∈pingMask P D from hx)]; unfold U firePlate; rw [runBy V,runBy V]
 have hz:WindowTag Z o (j*P.B+12) (Px+Px):=by
    refine ⟨⟨Girt.rite_c _,fun _ _ _ _=>rfl,fun x=>?_⟩,?_,fun x=>?_ ,fun _ _ _=>rfl⟩
    · have hf:= M.ticket.allV X; rw [h X hx] at hf; exact hf
    · intro g y; have hp:= M.rolls g X; rw [h X hx,h _ (show Lattice.gauge g J.1∈_ from (pingB J.1 g).mpr hx)] at hp; exact hp
    have hp:= M.price X; rw [h X hx] at hp; exact hp
 refine ⟨hz,hz.ticket,fun x=>(show Sector (modesIn N S_) false (U x) from (he x) ▸ (show Sector (modesIn N S_) false ((houseK P D U) J) from Vx.oscillator J)),fun x=> ?_⟩
 change acts (star (onsiteOne A (J.1,K J))) (mateK N)=acts (star (U x)) (mateK N); rw [← he x, ←h (J.1,K J) hx]; exact Vx.bra J
end YM.CF.Swell.Porticus
