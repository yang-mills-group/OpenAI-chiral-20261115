import GaugeFieldConstruction.AcrossElect
import GaugeFieldConstruction.AcrossVolume
import GaugeFieldConstruction.AmberOasisVU
import YM.SU5.FiniteGaugeData.Tapestry.Concatenation
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Reconstruction Tapestry.Altitude Tapestry.Exhibition PhaseChoice
open _root_.YM.OS.Ground TopologicalSpace
namespace Spine
variable {P : Spine} {s i k : ℕ}
open AcrossLands
open Py.Rate.AcrossShots VolumeRate
variable (P) (v:ℕ→ℝ)
local notation "Γ" => P.par
local notation "Y" => P.run
local notation "C" => P.diagonalᵢ
local notation "K" => P.diagonalₖ
local notation "B" => P.large
open AcrossLands Tapestry Preparation AcrossShots
variable {n:ℕ}
-- Lift along multiple kinds of paths; poll menu aperture fixed before horizons.
-- Include uniform over ALL k in the sampling column paying the cone gate. Plus supports and moment charges.
-- `pinligature` precisely the product-last detector probe (no absolute value).

abbrev panelCost (i k:ℕ)(A:BillsSumVU P):ℂ:= AcrossLands.position (mesh ((Y).ir i) (Γ).R.L ((Y).uv k)) (Γ).U ((Y).meter.a ((Y).uv k)) (v ((Y).uv k)) (witnessCutVU P i k A)

section
variable {R:P.Register}{ε:ℕ→ℝ}
variable (E:IntervalsSchedule P n v ε)

-- cf. supported tests (CedarSwimVU.productionTopVU), extends it to arbitrary indices after the width request.
lemma wide_cost {l:BillsSumVU P} (p:∀ a∈l,a.1∈PolAt Y B s a.2)(q:∀ a∈l,IsCompact a.2)
    (d:l.Pairwise (fun a b=> Disjoint a.2 b.2)):
    ∀ᶠ i:ℕ in atTop,∀ k:ℕ, Pay Y s i k→ TenderΘVU s i k l:=by
 obtain ⟨c,pC⟩:= into_cabin (sumΘVU l) (cumulus_compactVU l q)
 filter_upwards [wide_calendar Y c] with i hu k hp
 have ho:atCutoff Y B i k (ΞProdVU l)=witnessCutVU P i k l:= atCutoffFullVU (P:=P) l p d hp hu pC
 refine ⟨hp,?_, ho,?_⟩
 · have ht: ∀ a∈l,∃ S:Finset Cover,P.FootBill i k a.2 a.1 S:=by
    intro a w; obtain ⟨S,x,e,v,_⟩:=P.atTop_flavor i k s _ (p a w) hp; exact ⟨S,v,x,e⟩
   choose! f k using ht; refine ⟨f,k, unwrap Y i c hu _ _ ?_⟩
   intro r h; obtain ⟨a,z,b⟩:=Finset.mem_biUnion.mp h
   have hx: a∈l:=List.mem_toFinset.mp z; exact pC (singleIncVU hx ((k a hx).2.1.contains b))
 intro μ; obtain ⟨A,B0,R'⟩:=identifyRevenue Y B i k s (inside_budget Y B (PolExpoVU p)) hp
 rw [ho] at A R'; exact ⟨A,(partitionIncome Y i k hp.1).1,B0,R'⟩

open Tapestry.Fashion
variable {x:P.Spectrum0 3}{c:P.Poll 3} (V:P.Selects R 3 x c) {l:BillsSumVU P}{η:ℝ} (p:∀ a∈l, IsCompact a.2) (e:∀ a∈l,a.1∈PolAt P.run P.large s a.2) (d:l.Pairwise (fun a b=>Disjoint a.2 b.2))(w:0<η)
local notation "m_" r:max=> P.period r
local notation "ψh" r:max t:max=> circuitDepth P (P.period r) t
local notation "Λ" i:max => PollavuVU P 3 c i
-- includes location tickets and all integrability.Cinema
abbrev pinligature {c:P.Poll 3} (v:ℕ→ℝ)(i j k:ℕ)(l:BillsSumVU P)(η:ℝ):Prop:=
   TenderΘVU (c i).t j k (l++PollavuVU P 3 c i) ∧
   TenderΘVU (c i).t j k (PollavuVU P 3 c i) ∧
   VolumeInk P.par.K P.par.U (P.run.meter.a (P.run.uv k)) (v (P.run.uv k)) (mesh (P.run.ir j) P.par.R.L (P.run.uv k)) ∧
   1/2 < ‖panelCost P v j k (PollavuVU P 3 c i)‖ ∧
   dist (panelCost P v j k (l++PollavuVU P 3 c i)/panelCost P v j k (PollavuVU P 3 c i)) (P.spirits R 3 x (ΞProdVU l)) < η ∧
   panelCost P v j k (PollavuVU P 3 c i)= P.torqueBare v (P.pollTicket 3 c i) j k ∧
   panelCost P v j k (l++PollavuVU P 3 c i)= P.torqueBare v (ΞProdVU l * P.pollTicket 3 c i) j k ∧
   (l++PollavuVU P 3 c i).Pairwise (fun a b=>Disjoint a.2 b.2)

include E V p e d w
lemma pollPaths : ∀ᶠ i:ℕ in atTop, ∀ (I K':ℕ→ℕ),
   Tendsto I atTop atTop → Tendsto K' atTop atTop →
   (∀ᶠ r:ℕ in atTop, P.shoulderTape n ε v (I r) (K' r))→
   (∀ s A,A∈shorter P.Test s → Tendsto (fun t=> P.torqueBare v A (I t) (K' t)) atTop (𝓝 (vistaTake Y B (P.talks R) A))) → ∀ᶠ r:ℕ in atTop,pinligature P (R:=R) (x:=x) (c:=c) v i (I r) (K' r) l η:= by
 let F:=ΞProdVU l; let Rf:= P.spirits R 3 x F; let Lt(i):= P.pollTicket 3 c i; let pF:= V.poll F s (inside_budget Y B (PolExpoVU e)); let G:= vistaTake Y B (P.talks R)
 let Hᵢ(i):= P.RatioOn R 3 c i F
 filter_upwards [CerealFairVU (j:=3) p e d, V.denominator_tends.norm.eventually (lt_mem_nhds (show 1/2 < ‖(1:ℂ)‖ by norm_num)), Metric.tendsto_nhds.mp pF.1 (η/2) (half_pos w)] with i h hh hg I K' t t' p' f
 let S:=(c i).t; let L:=Λ i; let T:= l++L; let U:=F*Lt i
 obtain ⟨q,u,gx,d⟩:= h c
 let w'(x)(v:x∈ L):x∈ T:=List.mem_append.mpr (Or.inr v)
 have hb:F∈shorter P.Test s:=inside_budget Y B (PolExpoVU e)
 have he:Lt i∈shorter P.Test S:= short_pinhole _ _
 have hv:=f S U ((shorter P.Test S).mul_mem (Altitude.climbs P.Test q hb) he); have ht:= f S (Lt i) he
 have hr:G (Lt i)≠0:= norm_pos_iff.mp (by change 1/2 < ‖G (Lt i)‖ at hh; linarith); have hu:=hv.div ht hr
 filter_upwards [Metric.tendsto_nhds.mp hu (η/2) (half_pos w), ht.norm.eventually (lt_mem_nhds hh), t.eventually (P.wide_cost u gx d),t.eventually (P.wide_cost (l:=L) (fun a m=>u _ (w' a m)) (fun a m=>gx _ (w' a m)) (List.pairwise_append.mp d).2.1), ((Y).uv_grows.tendsto_atTop.comp t').eventually_ge_atTop S,p'] with r X hn h' hu₁ z y
 let A:=I r; let B₁:=K' r; have hp:Pay Y S A B₁:= ⟨y.1.2,z⟩
 let D0:= h' B₁ hp; let T0:= hu₁ B₁ hp
 have he₁: panelCost P v A B₁ T=torqueBare P v U A B₁:=by
    unfold U F Lt; rw [← CerealEqVU (c:=c), ←prod_addVU]; unfold panelCost torqueBare consultPrice; rw [← D0.comp]; rfl
 have he₂: panelCost P v A B₁ L=torqueBare P v (Lt i) A B₁:=by unfold panelCost torqueBare Lt consultPrice; rw [← CerealEqVU (c:=c), ← T0.comp]; rfl
 refine ⟨D0,T0,P.independentCash v E ((Y).uv B₁) ((Y).ir A) y.1.1,he₂.symm ▸ hn,?_,he₂,he₁,d⟩
 change dist (panelCost P v A B₁ T / panelCost P v A B₁ L) Rf < η; rw [he₁,he₂]; exact lt_of_le_of_lt (dist_triangle _ (Hᵢ i) _) (add_halves η ▸ add_lt_add X hg)

-- extend *uniform in t* through whole cone for each chosen Poll menu.
lemma pollingFreedom :
   ∀ᶠ i in atTop,∀ᶠ r in atTop, ∀ k, legacy Y (m_ r) (ψh r k)→
    pinligature P (R:=R) (x:=x) (c:=c) v i (m_ r) (ψh r k) l η:=by
 filter_upwards [P.pollPaths v E V p e d w] with i hi
 let F(r k:ℕ):Prop:= pinligature P (R:=R) (x:=x) (c:=c) v i (m_ r) (ψh r k) l η
 let S(r k:ℕ):= legacy Y (m_ r) (ψh r k)
 choose f₀ hf using fun r=> (show ∀ᶠ t in atTop,S r t from cadence Y (P.circuitDepth (m_ r)) (P.circuitMono (m_ r)) (m_ r)).exists
 let A(r:ℕ):=∃ k,S r k∧¬F r k
 let f(r:ℕ):= if p:A r then p.choose else f₀ r
 have he: ∀ᶠ r in atTop,S r (f r):= Eventually.of_forall fun r=> by
      unfold f; split
      next p=> exact p.choose_spec.1
      next p=> exact hf r
 let H0:= P.jointPays v E he
 filter_upwards [hi P.period (fun r=> ψh r (f r)) P.law.pick.grow_i.tendsto_atTop H0.1 H0.2 (fun _ A h=> (P.supportsRead v R E A h).1.paths f he)] with r hx k z
 change F r (f r) at hx; by_contra hk; have hp:A r:= ⟨k,z,hk⟩; exact hp.choose_spec.2 ((dif_pos hp : f r= _) ▸ hx)
lemma pollOrder : ∀ᶠ i in atTop, ∀ᶠ r in atTop, ∀ᶠ k in atTop,
    pinligature P (R:=R) (x:=x) (c:=c) v i (m_ r) (ψh r k) l η:=
 (P.pollingFreedom v E V p e d w).mono fun i h=> h.mono fun r t=> (cadence Y (P.circuitDepth (m_ r)) (P.circuitMono (m_ r)) (m_ r)).mono t
lemma intoCore : ∀ᶠ i in atTop, ∀ᶠ r in atTop, pinligature P (R:=R) (x:=x) (c:=c) v i (C (2*r)) (K (2*r)) l η∧
    SummitInvoiceVU (R:=R) (x:=x) (s:=s) (c:=c) i (2*r) l η:=by
 have hp:Tendsto (fun r:ℕ=> 2*r) atTop atTop:= StrictMono.tendsto_atTop (φ:=fun r:ℕ=> 2*r) (by intro _ _ h; exact Nat.mul_lt_mul_of_pos_left h (by decide))
 have h:= (P.pollPaths v E V p e d w).mono fun i h=> h _ _ (P.di_i.tendsto_atTop.comp hp) (P.di_k.tendsto_atTop.comp hp) (P.thinPays v E) (fun _ A h=> (P.supportsRead v R E A h).2)
 filter_upwards [h,BiPayVU V p e d w] with i u v'; exact u.and (hp.eventually v')
#print axioms intoCore
#print axioms pollingFreedom
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
