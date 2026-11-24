import SatinThinVista

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
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=> P.nomadic
local notation "bK"=> P.engine
abbrev thresholdF (f:ℕ):=(P.run.meter.a f).B
abbrev labW (f:ℕ):= repeatD P.par P.width (P.thresholdF f)
def twiceT (X:Cover)(j:Axis):= 2*(nodeC X j).natAbs
abbrev rarePlot (f i:ℕ)(X:Cover): List (Site (side P.run i f)):= let a:= P.rootAt f i X; [(plane j 0).mills (N f i) a,a]
-- clearance stencil nonnumeric abstract
noncomputable abbrev frameRadius (j:Axis) := noonFrame.sup (fun x=> (x j).natAbs)
structure Plans (j:Axis)(X:Cover)(f:ℕ) (P:Spine):Prop where
 seat: (P.labW f:ℤ) ≤ nodeC X j
 test: ((frameRadius j:ℤ)+(P.calibration.ℓ:ℤ)) ≤ nodeC X j
-- pressure affordability input separately
lemma frame_rise {v:ℕ}(p:Plans j X f P) : Tower.region j 0 P.calibration.ℓ (frameOne (P.clockPlate f v X)):=by
 have he: 0≤ nodeC X j:= by have u:= p.seat; omega
 let z:= P.par.R.L.val^(v-f); have hp:1≤ (z:ℤ):=by exact_mod_cast (Nat.succ_le_of_lt (pow_pos P.par.R.L.property (v-f)))
 have hv: nodeC X j≤ P.clockPlate f v X j:=by change _≤ (z • nodeC X) j; rw [Pi.smul_apply,nsmul_eq_mul]; exact le_mul_of_one_le_left he hp
 intro i h; obtain ⟨g,_,tκ⟩:= mem_biUnion.mp h; obtain ⟨t,u,rfl⟩:=mem_image.mp tκ; have hg:(t j).natAbs≤ frameRadius j:= Finset.le_sup (f:=fun x:Cover=> (x j).natAbs) u; have hx:= p.test; change _ ≤ t j+P.clockPlate f v X j; omega
variable (g:Plans j X f P)
include g
lemma window_plan {k: ℕ}(u: (nodeC X j).toNat+P.labW f≤ (side P.run k f).val): node (P.rootAt f k X)∈ band (side P.run k f) j 0 (P.labW f):=by
 apply (band_spec ..).mpr; rw [rootAt,node_of,wrap_here]; let n:=side P.run k f; let a:= P.labW f; let b:ℤ:= nodeC X j; have hb: (a:ℤ) ≤ b:= g.seat; have hv:0 ≤ b:= (Int.natCast_nonneg _).trans hb; have hn:0<n.val:=n.property; change b.toNat+a ≤ n.val at u
 have hx:b.toNat <(More n).val:=by change _<n.val*2; have e := Nat.lt_of_le_of_lt (le_trans (Nat.le_add_right _ a) u) (show n.val<n.val*2 from by omega); exact e
 have h: ((wrap (More n) (nodeC X)) j - ((0:ℤ):Per (More n)))=↑b.toNat :=by rw [Int.cast_zero,sub_zero,←Int.cast_natCast,Int.toNat_of_nonneg hv]; rfl
 have hy:=congrArg ZMod.val h; rw [ZMod.val_natCast_of_lt hx,wrap_here] at hy; rw [hy]; exact ⟨by change a≤ b.toNat; omega,u⟩
lemma upper_terrain (v:(nodeC X j).toNat+P.labW f≤ (side P.run i f).val):outdoor (rural (P.thresholdF f)) (P.rarePlot j f i X):=by
   let u:= P.labW f; let y:=P.rootAt f i X; let V:=(plane j 0).mills (N f i) y; have hp: P.rarePlot j f i X= [V,y]:=rfl; have ht: u= ℓ+12+rural (P.thresholdF f):=rfl; unfold outdoor; rw [hp,List.pairwise_pair]; rw [show node V=_ from (plane j 0).nodex y,separation_comm]; have hy:= P.window_plan j X g v; have H0:= opposite_gap j 0 (by omega:u>0) _ _ hy (mem_image_of_mem ((plane j 0).anon _) hy); exact lt_of_lt_of_le (by omega:_<2*u) H0
-- cow member proof. 
lemma rooting_cows (s:Axis): cows s (upperRoll (P.rarePlot j f i X)) (twiceT X j):=by
 let N':= side P.run i f; let x:=nodeC X; let u:=x j; let q:= wrap N' X; let p':= plane j 0; let v:=p'.mills N' q; have hp: upperRoll (P.rarePlot j f i X)={node v,node q}:=by rw [show P.rarePlot j f i X=[v,q] from rfl]; simp [upperRoll]; -- duplicates OK
 rw [hp]; have hv:(node q)=wrap _ x:= node_of ..; have ht(s:Axis): (node v) s=(wrap (More N') (p'.motion x)) s:=by rw [Shape.nodex,hv, Shape.anno] -- orientation?
 have hq:P.labW f ≤ u:= g.seat; have hw:0≤u:=by omega
 rcases eq_or_ne s j with rfl|j'; · refine ⟨-u,fun k w=>?_⟩; rw [mem_insert, mem_singleton] at w; cases w with
                                     | inl w=> subst k; exact ⟨-u,le_rfl,le_add_of_nonneg_right (by positivity), by rw [ht,wrap_here, show p'.motion x s=-u from ?_]; rw [show p'=plane s 0 from rfl,fling_move]; simp; rfl⟩
                                     | inr w=> subst k; exact ⟨u,neg_le_self hw,by change u≤ -u+((2*u.natAbs:ℕ):ℤ); omega,by rw [hv,wrap_here]⟩
 have h1:p'.motion x s= x s:= by rw [show p'=plane j 0 from rfl,fling_move]; exact if_neg j'.symm
 refine ⟨x s,?_⟩; intro k e; rw [mem_insert,mem_singleton] at e; refine ⟨x s, le_rfl,le_add_of_nonneg_right (by positivity),?_⟩; rcases e with e|e <;> subst k; · rw [ht,wrap_here,h1]
 rw [hv,wrap_here]
variable (p: f ≤ r)(q:r ≤ v)(b z:ℝ)
omit g
abbrev wakes (P:Spine)(j:Axis)(f i k:ℕ)(X: Cover){r v:ℕ}(p:f≤r)(q:r≤v)(b z:ℝ): Mark (Journey.side P.run i v) := ((P.rarePlot j f i X).map (gapMark P.run i k b z p q)).prod -- Y variable shadow!
lemma shine (u:(P.run.voyage i).kick ≤ k)(w:v≤ P.run.uv k) : P.wakes j f i k X p q b z= let Z:=gapMark P.run i k b z p q (P.rootAt f i X); reflMark j 0 Z*Z:=by
 unfold wakes rarePlot; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one, gap_swing _ _ _ _ _ _ u w, highTurn,mul_zero]
abbrev flume (v:ℕ)(g:Plans j X f P):P.Vox j v:= P.positiveVox j v (frameOne (P.clockPlate f v X)) (P.visitOne v (P.clockPlate f v X)) ((Tapestry.locates ..).mpr P.basesT) (P.frame_rise _ _ g)
-- assembled arithmetic input: support geometry scenarios earned at purchase. report criterion
abbrev repeatBill (P:Spine)(d f:ℕ):= 14*Worth.meterC (hat P.par.R.L P.par.x f)*(((4*(d+plusAgain P.par.block (P.labW f)):ℕ):ℝ))^4≤1
variable (G:P.repeatBill (twiceT X j) f)(O:P.NightCop)
include g G O
lemma plan_clock (d:ℝ):∀ᶠ i:ℕ in atTop,∀ b z t:ℝ,ShelterCost C Y f (P.nomadic i) (bK i) → ReadDensity Y (P.nomadic i) (bK i) A p q b z t→(∀ x:Fields (side P.run (P.nomadic i) v),‖P.wakes j f (P.nomadic i) (bK i) X p q b z x‖ ≤ d)→ ‖Journey.compass P.run (P.nomadic i) (P.engine i) v (P.wakes j f (P.nomadic i) (bK i) X p q b z)‖ ≤3*owedF P.par f A 2 :=by
 let T:=P.thresholdF f; let J:=P.labW f; let B:=twiceT X j; let D:= plusAgain Q J; let R:=owedF P.par f A 2
 have hr:Tendsto (fun i=>((Journey.side P.run (aK i) v).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (P.amount_go v)
 filter_upwards [O v,P.history.finance v,hr.eventually_ge_atTop (d*(16/R)), (P.amount_go f).eventually_ge_atTop (B+D), (P.amount_go f).eventually_ge_atTop ((nodeC X j).toNat+J)] with i Z V ht e n b z t Yp Pp h
 have hp:= V.depth; have hv:= V.enters; let U:= aK i; let k:= bK i; have hf:f ≤ P.run.uv k:= le_trans (p.trans q) hv; have hy: (RootBook Y U k f).p.B=T:= (congrArg BudgetPoint.B (Papal.prices_plot P.run f U k hf).1); let S:= rarePlot P j f U X
 exact compass_clock P.run U k p q S Yp Pp (by rw [hy]; exact e) (by rw [hy]; exact G) H V Z ht (by rw [hy]; exact P.upper_terrain j X g n) rfl h (P.rooting_cows j X g)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.plan_clock
