import YM.SU5.Same.TemperScout
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)

/-! # Subsidy ratios on a single width series. Make this choice BEFORE committing
any prism or smooth probe. The shipping ratios are obtained as in `SatinThinBank`
(using only product of intervals on a countable tier), not assuming a unique
choice of limiting clover wave normalization. -/
variable {P}
local notation "Tier"=>ℕ × ℕ
structure Earnings(P:Spine)(A C:ℝ)(g h:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ): Prop where
 fast:StrictMono v
 up:∀ i, h ≤ v i
 cruise:∀ i,∃ c w, Workforce A C g (v i) P c (a i) w
 earlier:g<h
variable {v':ℕ→ℕ}{a:ℕ→(ℕ×ℕ)→ℝ} {A C b:ℝ}{g h:ℕ}
variable (E:Earnings P A C g h v' a)
lemma ScoutAnthem.rides {x:P.Spectrum0 3}(e:g<h)(u:ScoutAnthem P x A C g h b v' a): Earnings P A C g h v' a:=by obtain ⟨R,t⟩:=u.station; exact ⟨t.fast,t.up,t.cruise,e⟩
lemma ScoutAnthem.move {x:P.Spectrum0 3}(h:ScoutAnthem P x A C f r b v' a) {κ:ℕ→ℕ}(p:StrictMono κ): ScoutAnthem P x A C f r b (v'∘κ) (a∘κ) :=by
 obtain ⟨⟨d,q⟩,k⟩:=h; exact ⟨⟨d,⟨q.fast.comp p, fun i=>q.up _,fun i=>q.cruise _,q.price,fun i=>q.main _,fun n=> p.tendsto_atTop.eventually (q.extra n)⟩⟩,fun j l w h=> (k j l w h).imp fun B t=>p.tendsto_atTop.eventually t⟩
lemma AtGlassRate.carries {x:P.Spectrum0 3}{l:List Axis}(h:AtGlassRate P x j f r l v' a){κ:ℕ→ℕ}(p:StrictMono κ): AtGlassRate P x j f r l (v' ∘ κ) (a∘κ):=by obtain ⟨B,q,K,k,h⟩:=h; exact ⟨B,q,K,k,h.mono fun i t=> p.tendsto_atTop.eventually t⟩ -- B notation?
include E
lemma Earnings.pick (u:g ≤ f)(v:f < r)(x:r≤ v' i): ∃ (w:ℕ→ℝ) (l:ℕ→ℕ), lender A C f r (v' i) w (a i (f,r)) l P:=by
 obtain ⟨c,w,t⟩:=E.cruise i; exact ⟨_,w,t.plans (f,r) (show chargeSpan g (v' i) (f,r) from ⟨u,v,x⟩)⟩
omit E
lemma cradle_strict {x:ℝ} (p:P.cradle r v x): x≠0:=by rintro h; have ht:=p.2; rw [h,abs_zero,mul_zero] at ht; exact one_pos.not_ge ht
noncomputable def subsidy (g h f r i:ℕ)(a:ℕ→(ℕ×ℕ)→ℝ) := a i (g,h)/a i (f,r)
noncomputable abbrev avail (Λ':Lattice.Side) (h r:ℕ): ℝ:=4*zoomC Λ'^(r-h)
lemma fee_pos (P:Spine) : 0<avail P.par.R.L h r:= by unfold avail; have he:=zoomC_p P.par.R.L; exact mul_pos (by norm_num) (pow_pos (zero_lt_one.trans_le he) _)
include E
lemma Earnings.gift (u:g≤f)(p:f<r)(t:h≤f)(x:r≤v' i): |subsidy g h f r i a|≤ avail P.par.R.L h r ∧ subsidy g h f r i a * a i (f,r) = a i (g,h):=by
 obtain ⟨c,w,S⟩:= E.cruise i; have ht:chargeSpan g (v' i) (g,h):= ⟨le_rfl,E.earlier,E.up i⟩; have hx:chargeSpan g (v' i) (f,r):=⟨u,p,x⟩; have he:=cradle_strict (S.plans (f,r) hx).cape; unfold subsidy; rw [abs_div]; exact ⟨(div_le_iff₀ (abs_pos.mpr he)).2 (S.career (g,h) (f,r) ht hx (t.trans p.le)), div_mul_cancel₀ _ he⟩
omit E
noncomputable def PaidSubsidy (g h:ℕ)(a:ℕ→(ℕ×ℕ)→ℝ) : Prop:=∀ f r:ℕ,g ≤ f→h≤ f→ f<r→ CauchySeq (fun i=> subsidy g h f r i a)
include E
lemma Earnings.forks : ∃ κ:ℕ→ℕ, StrictMono κ ∧ PaidSubsidy g h (a∘κ):=by
 let X:= Tier → ℝ
 let V(s:Tier):= Set.Icc (-avail P.par.R.L h s.2) (avail P.par.R.L h s.2)
 let U(i:ℕ)(j:Tier):=subsidy g h j.1 j.2 i a; let k(i:ℕ)(j:Tier):ℝ := if U i j ∈ V j then U i j else 0
 have he(i:ℕ)(j:Tier): k i j∈ V j:=by unfold k; split; assumption; exact abs_le.mp (show |0|≤ avail (L) h j.2 from (abs_zero.le.trans (P.fee_pos (h:=h) (r:=j.2)).le))
 obtain ⟨a',hv,t,u,e⟩:= (isCompact_pi_infinite (ι:=Tier) (X:=fun _=>ℝ) (fun i:Tier=>show IsCompact (V i) from isCompact_Icc)).tendsto_subseq (x:=k) (fun i=>he i) -- binder in s! fix
 refine ⟨t,u, fun f r v x y=> Tendsto.cauchySeq ((tendsto_pi_nhds.mp e (f,r)).congr' ?_)⟩
 filter_upwards [((E.fast.comp u).tendsto_atTop.eventually_ge_atTop r)] with i w
 change k (t i) (f,r)= U (t i) (f,r)
 exact if_pos (abs_le.mp (E.gift v y x (show r≤v' (t i) from w)).1)
-- quote purchasing across all widths follows from these path witnesses.
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.Earnings.forks
#print axioms Spine.ScoutAnthem.move
#print axioms Spine.AtGlassRate.carries
