import YM.SU5.Registration.Affine.Detent
import YM.SU5.Registration.Affine.Rated
import YM.SU5.Registration.Rise.Flying
import YM.SU5.Registration.Rise.StowAt
import YM.SU5.Registration.Rise.GranuleSpace
import YM.SU5.Registration.Rise.Rally
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
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 
open Worth Pays CF.BProof

/-! # Clock-column long estimates in this election. From phase-independent prices
on mean to ANY spectrum point including x chosen to read the thin probes. Width of
each box MUST stay common here over every tall-scale actor arm of the comparison.
ClockBooking's earned bound is applied at level v (changed coarse-phase probe),
using long banner & No cheap error estimate at volume varying with height.
-/
open SlabMark.ClockBooking
open Aria Casting MacroGrid
local notation "β"=> ruler P.par.block
local notation "β'"=> (16*P.par.block.val:ℕ)
local notation "Z" f:max v:max w:max=> ((P.par.R.L.val:ℕ)^(v-f)*w:ℕ)

/-! # Operator at ANY heated presentation

Maps from fields at a fixed anchor into a taller stage (ruler-overlap fixed) are
in H and are contractive; can pass to ALL matter-free clock leaves in one
norm estimate. When the allowance is spent at both ends the opening line is
operator-norm priced; the screenings at nonaligned points depend on mesh, but
transfer out of mesh on MANY-F via its spatial continuity. Then get Strong Star Cauchy
on the sequence of managed granules.
-/
open Germ Alliance
open _root_.YM.SatinRegistration
variable (xY x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x j
local notation "X'"=> P.ColorHil j ξ
local notation "G"=> P.ManyF j ξ
local notation "U"=> P.truck j ξ
local notation "E"=> (P.physicalEnergy j ξ).E
local notation "S"=> P.seasons j ξ
local notation "E'" => (S).E
local notation "T'"=>timeMesh P.par
local notation "α" s:max n:max => whenly (timeMesh P.par) s n
local notation "π" => P.toStageG j ξ
variable (g h:ℕ)(l:List Axis) (a:ℕ→(ℕ×ℕ)→ℝ)(v':ℕ→ℕ)
local notation "s!"=> P.rootSpace g f l
local notation "p!" n:max=> P.quoteSpot g f l n
local notation "O" f:max=>P.rowClock j g f l
local notation "π'" n:max=> P.basePlay x g n
local notation "D" n:max=> (P.basePlay xY g n).pivot P l
local notation "c₀"=>ℕ -- remove
local notation "z₀" v:max=> (Z f v (O f))
local notation "Z'" v:max=> P.bedCase j (P.rootSpace g f l) xY (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) v
local notation "Cκ" v:max=> (Z' v).charges ξ (P.calendarZ v f (O f) (Nat.succ_pos _))
local notation "κ" => P.cartage j ξ
local notation "ℓ₁" v:max=> ((p! v) j).toNat -- parser ℓ! not p! max!!
local notation "λκ" v:max=> (p! v)
local notation "J" s:max t:max=> P.pitCab j x g l f s t
variable (Y₀:P.NightCop) (L':Odd P.par.R.L.val) (D₀:Earnings P A C g h v' a)
local notation "T" v:max=> (a v (g,h):ℂ)
local notation "b!" v:max=> (a v (f,r):ℂ)
noncomputable def tenderH (t:ℝ≥0)(v:ℕ): (P.ColorHil j (P.advocate 3 x j)).Op:=
 ((a v (g,h):ℝ):ℂ) • P.stageH j ξ ((P.basePlay xY g (v' v)).pivot P l) t t

local notation "Ξ" r:max v:max t:max=> (J (v' v) t) (Cκ r)
local notation "λ₀" f:max r:max v:max=> subsidy g h f r v a
noncomputable def approxCane (f r:ℕ)(t:ℝ≥0)(v:ℕ) := ((subsidy g h f r v a:ℝ) :ℂ) • P.pitCab j x g l f (v' v) t ((P.bedCase j (P.rootSpace g f l) xY (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) r).charges ξ (P.calendarZ r f (O f) (Nat.succ_pos _))) -- check hygiene shadow f note O f macro f argument passed OK
local notation "pC" r:max t:max i:max=> P.approxCane j xY x g h l a v' f r t i
local notation "Z₀" t:max i:max=> P.tenderH j xY x g h l a v' t i
local notation "D'" f:max=>6*tiltBase P.par A f
variable (p:h≤ f)(b0:f<r)
private lemma advance_spend_currency (X:Hilbert)(A B:X.Op)(k μ' c:ℝ)(h:k*μ'=c)(f:X.Op→L[ℂ]X.Op)(Y':X.Op)(u:Y'=f A): (c:ℂ) • Y' - (k:ℂ) • f B=(k:ℂ) • f ((μ':ℂ) • A - B):=by rw [u,map_sub,map_smul,smul_sub,smul_smul,←Complex.ofReal_mul,h]
include p b0 Y₀ L' D₀
lemma relative_tender 
    (Yκ:P.ColumnBill (P.rowClock j g f l) f) (t:ℝ≥0)(gF:α f (O f)≤ t) (y:r≤v' i)(w:P.StampHere j (D (v' i)) (v' i) (Z f (v' i) (O f)) (p! (v' i))): ‖(Z₀ t i)-(pC r t i)‖ ≤ skyLoss P A f r h:=by
 let hG:= D₀.earlier.le.trans p; let K:= D₀.fast.tendsto_atTop

 let v:= v' i; let t':= P.bedCase j (P.rootSpace g f l) xY (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1)
 let g':= P.calendarZ r f (O f) (Nat.succ_pos _); let δ:= a i (f,r); let A':= Cκ r; let B:= Cκ v; let C':= P.pitCab j x g l f v t; let k:= subsidy g h f r i a; obtain ⟨u',π0⟩:= D₀.gift hG b0 p y
 obtain ⟨g₁,v₁,h₁⟩:= D₀.pick hG b0 y
 have he:‖(δ:ℂ) • B-A'‖ ≤ 2*(6*tiltBase P.par A f/(zoomM P.par.R.L^(r-f))):= P.gap_detent j (P.rootSpace g f l) xY x (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) (Nat.succ_pos _) h₁ Yκ Y₀ b0.le y
 have hz: P.stageH j ξ (D v) t t=C' B:= by
    let e: f≤v:=b0.le.trans y; rw [P.footprint_paid j (0:Cover) xY x g 0 l _ t w (P.quote_spot_agrees g l hG L' e) gF e]; exact (P.pit_reads ..).symm
 have hV: (Z₀ t i)-(pC r t i)= (k:ℂ) • (C' ((δ:ℂ) • B - A')):=advance_spend_currency X' B A' k δ (a i (g,h)) π0 C' _ hz
 rw [hV,norm_smul,Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul u' ((P.pit_pay ..).trans he) (norm_nonneg _) ((abs_nonneg k).trans u')
lemma zone_tender (Yκ:P.ColumnBill (P.rowClock j g f l) f) (t:ℝ≥0)(gF:α f (O f)≤ t) : ∀ᶠ i:ℕ in atTop,∀ γ:P.Spectrum0 3, ‖P.tenderH j xY γ g h l a v' t i-P.approxCane j xY γ g h l a v' f r t i‖ ≤ P.skyLoss A f r h:=by
 filter_upwards [D₀.fast.tendsto_atTop.eventually_ge_atTop r,D₀.fast.tendsto_atTop.eventually (P.quote_fits j xY g l (D₀.earlier.le.trans p) L')] with i v₀ v₁
 exact fun t' => P.relative_tender j xY t' g h l a v' Y₀ L' D₀ p b0 Yκ t gF v₀ v₁

-- point-$γ$ movement aligned. Here comp spacecraft depends on γ.
local notation "uᵃ" i:max=> (P.laysM (P.vtile (v' i) (p! (v' i))))
local notation "τ" t:max =>Real.toNNReal t
local notation "uℓ"=> fun j:Axis=> P.pinTime j g f l
local notation "s₀" i:max=> α (v' i) (ℓ₁ (v' i))
local notation "w"=> α f (O f) -- notation w binder issue from earlier? after proof.
local notation "η"=> (τ (P.pinTime j g f l))
omit p b0 Y₀ L' D₀ in
noncomputable def ticketsInSpace (t:ℝ≥0)(r:ℕ)(z:ℂ) : (P.ManyF j (P.advocate 3 x j)).Op:= z • P.cane x j (E' (t-η)* (π (Cκ r)) * E' (t+η-(α f (O f)))) (- (fun j:Axis=> P.pinTime j g f l)) -- check `include p b0` appended F etc double binder r due dependent P'. `include` before def includes r etc -> BAD! move omit then include
local notation "θ" i:max => ((uᵃ i)- (fun j:Axis=>P.pinTime j g f l))
local notation "v₀" i:max=> P.vtile (v' i) (p! (v' i))
omit p b0 Y₀ L' D₀ in
lemma approx_here (t:ℝ≥0)(i:ℕ) : P.cane x j (π (pC r t i)) (θ i)= ((λ₀ f r i):ℂ) • P.cane x j (E' (t-(s₀ i))* π (Cκ r) * E' (t+(s₀ i)-w)) (- (fun j:Axis=>P.pinTime j g f l)):=by
 let b':= (pC r t i); let a₀:=θ i; let u:=v₀ i; let X:=Cκ r; let z:ℂ:= λ₀ f r i; let p:= p! (v' i)
 change P.cane x j (P.toStageG j ξ (z • (J (v' i) t) X)) a₀ =_
 rw [map_smul,P.pit_reads,P.charter_toG,P.lays_neg,neg_neg,P.bank_both,←P.cane_scaled]
 change z • P.cane x j (κ (-(P.laysM u))*(E' (t-(s₀ i))* π X * E' (t+(s₀ i)-w))*κ (P.laysM u)) a₀=_
 have he(B:(G).Op): (κ (-(P.laysM u))*B*κ (P.laysM u))=P.cane x j B (-(P.laysM u)) :=by unfold cane; rw [neg_neg]
 rw [he,P.cane_join]; congr 2; unfold a₀ u; rw [sub_eq_add_neg]; abel

-- can now use aligned comparisons. note include p etc helps pin positive of η.
variable (Tq:∀ᶠ s:ℕ in atTop,treasury A C P s (s+1) (s+1))
lemma price_in_space {z:ℂ}(v₁:Tendsto (fun i:ℕ=> (↑(subsidy g h f r i a):ℂ)) atTop (𝓝 z))(t:ℝ≥0)(u: w ≤ t) : Agrees atTop (fun i γ=> P.cane γ j (P.toStageG j (P.advocate 3 γ j) (P.approxCane j xY γ g h l a v' f r t i)) (θ i)) (fun _ γ => P.ticketsInSpace j xY γ g l (f:=f) t r z):=by
 let d:=P.pinTime j g f l; let a₀:=d.toNNReal
 have he:0<d:= P.pin_p ..; have hc:0<a₀:= Real.toNNReal_pos.mpr he; have hb:a₀<t:=by have hh:= (P.pin_covered j g l (f:=f)).trans_le (show ((α f (O f)):ℝ) ≤ (t:ℝ) from u); apply (NNReal.coe_lt_coe).1; rw [Real.coe_toNNReal d he.le]; exact hh
 have ht:0<t-a₀:=tsub_pos_of_lt hb
 have hz:0<t+a₀-w:=tsub_pos_of_lt (u.trans_lt (lt_add_of_pos_right t hc))
 let Hx(γ):=P.seasons j (P.advocate 3 γ j)
 let L₀:= P.bedCase j (P.rootSpace g f l) xY (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) r
 let k:= P.calendarZ r f (O f) (Nat.succ_pos _)
 -- M is uniform for that one (even if distance epsilon selects huge r in getting it).
 let C (γ):= P.toStageG j (P.advocate 3 γ j) (L₀.charges (P.advocate 3 γ j) k)
 let B:=‖P.Box j r (Z f r (O f)) k L₀.card‖
 have hC:OnTab atTop (fun (_:ℕ) γ=> C γ):=⟨B,norm_nonneg _,Eventually.of_forall fun i γ=> (P.toG_cost ..).trans (L₀.cap _ k)⟩
 let X(i:ℕ)(γ):=(Hx γ).E (t-(s₀ i)); let U'(i:ℕ)(γ):=(Hx γ).E (t+(s₀ i)-w)
 let S₁(i:ℕ):=(s₀ i)
 have hG:Tendsto S₁ atTop (𝓝 a₀):= (P.quote_time_val j xY g l (D₀.earlier.le.trans p) L').comp (D₀.fast.tendsto_atTop)
 have hx: Agrees atTop X (fun _ γ=> (Hx γ).E (t-a₀)):= same_heat Hx ht (tendsto_const_nhds.sub hG)
 have hy: Agrees atTop U' (fun _ γ=> (Hx γ).E (t+a₀-w)):= same_heat Hx hz ((tendsto_const_nhds.add hG).sub_const w)
 let V:=fun j:Axis=> P.pinTime j g f l; let A'(γ):= P.cartage j (P.advocate 3 γ j) (-V); let B'(γ):= P.cartage j (P.advocate 3 γ j) (- -V)
 have u0:OnTab atTop (fun (_:ℕ) x=>A' x):= ⟨1,zero_le_one,Eventually.of_forall fun i γ=>P.cart_pay ..⟩; have v0:OnTab atTop (fun (_:ℕ) γ=>B' γ):= ⟨1,zero_le_one,Eventually.of_forall fun i γ=>P.cart_pay ..⟩
 let G'(i:ℕ):ℂ:= subsidy g h f r i a -- h shadows ht Tendsto. Rename
 have h1:OnTab atTop X:=OnTab.keeps1 Hx _; have h2:OnTab atTop U':= OnTab.keeps1 Hx _
 let p0:= (h1.prod hC); have hh:= (hx.prod (Agrees.refl (fun _ x=> C x)) h1 hC).prod hy p0 h2; let W₁:=p0.prod h2
 let g' := ((Agrees.refl (fun _ x=>A' x)).prod hh u0 W₁); let W₂:=u0.prod W₁
 let y:=g'.prod (Agrees.refl (fun _ x=> B' x)) W₂ v0; let W₃:=W₂.prod v0
 have ha: Agrees (b:=fun _ : P.Spectrum0 3=>ℂ) atTop (fun i γ=> G' i) (fun i γ=>z):= fun ε c=> ( (Metric.tendsto_nhds.mp v₁ ε c)).mono fun i h γ=> h.le
 have hw:OnTab atTop (fun (_:ℕ) (_:P.Spectrum0 3)=>z):=⟨‖z‖,norm_nonneg _,Eventually.of_forall fun _ _=>le_refl _⟩
 apply (SatinRegistration.of_eq ?_).trans (y.scaled ha W₃ (hw.rotate ha.symm)); refine Eventually.of_forall (fun i=> funext fun γ=>?_); exact P.approx_here j xY γ _ _ l a v' t i -- can unfold Q

-- etc align in next file. Need not include Tq. strip comments before submit cleanup
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms zone_tender
#check @ticketsInSpace
#print axioms approxCane
#print axioms price_in_space
