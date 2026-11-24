import WakeRoad.Wilga
/-! # Oriented comparisons and deck legality. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Buffered Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Skye Precision Tree Fock
attribute [local instance] opCStarAlgebra
open PhysicalNext.JointLoad.Heir
open YM.WakeRoad CF.Pannier.Chancel Rous Pressure Papal EmberWind Work.E08
open Gleam Regis Regis.Head Gleam.Wake
open CF.Gingham.Ruff
local notation "G₅"=> SU.group
open CF.Gingham.Ruff
namespace ArborJet
variable {N:Side}{m d s:ℕ}{S:Support (More N)}
local notation "M"=> Signed.mirror (3:Axis)
open Afterglow Journey Tapestry CF.WakeInvestment Vale
open Lamour.Bridge Celeste Clock Hookah
open Regis.Wake
open scoped ContDiff

open CF.Gingham.Ruff CF.Buffered.Afterglow.Tower.VacuumSelection CF.BProof
open Pressure.Worth Pressure.Worth.Pays
open Spine.Gingham.VoyageB Spine.Gingham
variable (P:CF.Buffered.Afterglow.Tower.VacuumSelection.Spine)
local notation "Y"=>P.run
local notation "Λ"=>P.par
abbrev moment (s:ℕ):ℕ:= zoomR P.par 12 s
abbrev stanceR (s:ℕ):ℤ:= -(moment P s:ℕ) -- negative Nat parses annotation? coercion?
def tube(s:ℕ):ℕ:=4*moment P s
abbrev mast :ℝ:=66
local notation "xₛ" s:max=>hat P.par.R.L P.par.x s
local notation "bₛ" s:max=>radiusB (hat P.par.R.L P.par.x s)
private lemma fields : ∀ᶠ s in atTop, (↑(2*tube P s):ℝ) ≤ sPow P.par s mast ∧
    (∀ N:Side,(↑(BlockP (tube P s) (0:Seat N)).card:ℝ) ≤ sPow P.par s mast) ∧ bₛ s+2+debt+12 ≤ moment P s:= by
 have H := Worth.Pays.rising
 have hc (b:ℝ):Pays 0 0 2 (fun _=>b):=Worth.Pays.merit (constant _) (by norm_num [Worth.Earlier]);
 have r: Pays 0 0 2 (fun x:ℝ=> (radiusB x+2+debt+12:ℕ)):= by push_cast; exact plus (plus (plus H (hc _)) (hc _)) (hc _)
 let Q(x:ℝ) := BProof.coin x 0 13 0
 let F(x:ℝ):=8*Q x+1
 have hp:Pays 0 13 0 F:=plus (Pays.scale 8 (whole 0 13 0)) (Worth.Pays.merit (constant 1) (by norm_num [Worth.Earlier]))
 filter_upwards [GramSignal.zoom_pays (P:=P) 12 (by norm_num), (turnover P.par).eventually (leap hp (show Earlier 0 13 0 0 mast 0 from Or.inr (.inl ⟨rfl,by norm_num [mast]⟩))), (turnover P.par).eventually (leap (pot hp 4) (show Earlier _ _ _ 0 mast 0 from by norm_num [Earlier,mast])),(turnover P.par).eventually (leap (Pays.scale 2 r) (show Earlier 0 0 2 0 12 0 from by norm_num [Earlier])) ] with s h a e t';norm_num at h
 let z:= xₛ s
 change (↑(moment P s):ℝ) ≤ Q z at h
 have hx:(↑(2*tube P s):ℝ)+1 ≤ F z:= by unfold tube F; push_cast; linarith only [h]
 refine ⟨(le_trans ?_ hx).trans a, fun N=> ?_,?_⟩; · simp
 · apply le_trans (b:=F z^4) _ e; refine le_trans (Nat.cast_le.mpr (show (BlockP _ _).card ≤ (2*tube P s+1)^4 from ?_)) ?_; swap
   · push_cast; gcongr; push_cast at hx; linarith
   have t:=Corona.halo_size {(0:Seat N)} (tube P s)
   rwa [card_singleton,one_mul,←two_mul] at t
 have he:(↑((bₛ s)+2+debt+12):ℝ) ≤ (↑(moment P s):ℝ):= by
    let x:=sPow P.par s 12; have h₁:x/2 ≤ (↑(moment P s):ℝ):=Nat.le_ceil _; change 2*((_ :ℕ):ℝ) ≤ x at t'; linarith only [t',h₁]
 exact_mod_cast he

lemma tubescape (s:ℕ)(b:Bool)(h:bₛ s+2+debt+12 ≤ moment P s):going (N:=N) (stanceR P s) b (bₛ s+2)⊆ BlockP (tube P s) (0:Seat N):=by
 let m:=moment P s
 let t₀:=2 • stanceR P s • (step (3:Axis):Cover)
 have he(i:Axis): t₀ i = if i=3 then -(2*m:ℤ) else 0:=by unfold t₀ stanceR; simp [step,m]; simp [Pi.single_apply]; split <;> ring_nf
 have hc (k:Axis): |t₀ k| ≤ 2*m:= by rw [he]; split<;>simp
 have u: separation (0:Seat N) (homebase (N:=N) (stanceR P s) b)≤2*m:=by
    cases b; · simp [homebase]
    let H: t₀∈Lattice.box (2*m):=box_test.mpr ⟨fun i=>(by have :=(abs_le.mp (hc i)).1; push_cast; exact this),fun i=>(by push_cast; exact (abs_le.mp (hc i)).2)⟩
    simpa [homebase,t₀] using separation_box_add (0:Seat N) H
 intro i v; replace v:=blocks_test.mp v; apply blocks_test.mpr; have ht:=separation_triangle (0:Seat N) (homebase (stanceR P s) b) i; change _ ≤ 4*m; omega

local notation "v*" s:max i:max=> side P.run i s
local notation "?R?" s:max i:max k:max=> RootBook P.run i k s
variable (s i k:ℕ){a c μ:ℝ}{l:ℕ}(B:Scene P a c μ l s i k){δ C:ℝ}(X:Rialto 6 P.par.d δ C)
local notation "Bₘ"=> (RootBook P.run i k s).p.B
local notation "Φ"=> Bₘ /10
local notation "Iₖ"=> Postcard (Bₘ /10)
local notation "ζ₀"=> stanceR P s
local notation "Ω"=> (side P.run i s)
-- universal receipts at these scales
abbrev filmT (δ h:ℝ)(b:Bool): Mark (side P.run i s):= ringmark (stanceR P s) b B.gb B.bre h δ -- δ implicit? explicit
abbrev grove (b:Bool):Vessel SU.group (More (side P.run i s)) (Postcard (Bₘ/10)):=elector _ (stanceR P s) b
abbrev cocoa : WakeRoad.Press (Postcard (Bₘ /10)):= atoms X B.gb.pump Bₘ
abbrev combo(b:Bool):= portrait b (cocoa P s i k B X)
lemma gaucho(R:ℝ)(D:Web SU.group)
  (v:Dawn δ D (underlay P.par) c a P.par mast s (?R? s i k).p R)(u:Arioso X B.gb.pump B.bre)
  (b:Bool)(t:going ζ₀ b (Bₘ+2) ⊆ BlockP (tube P s) (0: Seat Ω))
  (e:Bₘ=bₛ s)(d':2*(Bₘ/10+2)<(More (side P.run i s)).val):
  RowBook P.run s i k (q:=BlockP (tube P s) (0: Seat Ω)) (metricC (underlay P.par) c a) (supply δ (underlay P.par) c a (RootBook P.run i k s).p R)
  |riskM δ D (underlay P.par) c a P.par s (RootBook P.run i k s).p R| R (radiusB (hat P.par.R.L P.par.x s))
  (filmT P s i k B δ R b) (grove P s i k b) (combo P s i k B X b):=by
 let y:=(R:ℝ)
 have t': Bₘ/10+2≤Bₘ+2:=by omega
 let U:= B.gears.tag
 have h:=projected _ b B.gb B.bre U y δ t
 have h': Tagbill (4*(a/4)) 1 (underlay P.par) 2 P.par.J.n Bₘ:= by rw [show (4:ℝ)*(a/4)=a from by ring]; exact U
 obtain ⟨pl,g⟩:=magazine ζ₀ b X B.gb B.bre u U y
 refine ⟨h.1,h.2,signature _ _ t' t v.rent,?_,_,pl,ring_read _ b B.gb B.bre y δ,g,?_,?_⟩
 · unfold combo; rw [portrait_coin]; have hp:= atoms_fee X B.gb.pump h'
   unfold metricC cocoa; refine (mul_le_mul_of_nonneg_left hp (by norm_num)).trans ?_; exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one) -- meta
 · intro V; unfold supply; exact (paletron_sale ζ₀ b X B.gb B.bre u y V).trans ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))
 intro V h0; unfold riskM; let q:=chip_pos (hat P.par.R.L P.par.x s) (-120000)
 exact (scored ζ₀ b X B.gb B.bre u U D v.cutoff R _ _ t h0.1 q.le h0.2 v.calm d').trans (le_abs_self _)
#print axioms gaucho

variable (R:ℝ)(b:Bool)
local notation "F*" i:max=>filmT P s i -- incomplete
structure Huddle(R:ℝ) :Prop where
    single (b:Bool) : ‖Journey.compass P.run i k s (filmT P s i k B δ R b)- seatT P.run s i k (grove P s i k b) (WakeRoad.Score (combo P s i k B X b)) R‖ ≤ chip (hat P.par.R.L P.par.x s) (-3)
    joint : ‖Journey.compass P.run i k s (filmT P s i k B δ R true * filmT P s i k B δ R false)-seatT P.run s i k (planter (fun b=>grove P s i k (!b))) (brushpot (fun b=> combo P s i k B X (!b))) R‖ ≤ chip (hat P.par.R.L P.par.x s) (-3)
open Diary
variable (Mc:ℕ)(K:P.Register)
lemma collecta (E₀:ℝ)(v:Spine.PreparedInvestment P K E₀ Mc){Y':ℕ→Fleece P.calibration}{r:ℕ→ℕ}(Z:Lander P a c μ l r Y')(D:Web SU.group)
 (hδ:0<δ)(A:Anthem P a c μ l δ C X){ι:ℕ→ℕ}(g:Tendsto ι atTop atTop):
  ∀ᶠ s:ℕ in atTop, ∀ᶠ n:ℕ in atTop, let i:=irr P (r (ι n));let k:=uvv P (r (ι n))
                                    Nonempty (Scene P a c μ l s i k) ∧ ∀ (p:Scene P a c μ l s i k)(R:ℝ),|R|≤2*Real.sqrt (hat P.par.R.L P.par.x s) → Huddle P s i k p X R:=by
 obtain ⟨v₀,t⟩:= v.investment
 let hZ:=Z.grew.tendsto_atTop.comp g
 let H(n:ℕ):=(sails.{0} P.run P.law P.history t v.dispatch v.rocky.merit 0 n (show 0 < mast by norm_num [mast]) (show 0 < (1/2:ℝ) by norm_num) (by norm_num))
 -- big theorem may defeq period eq after thinning
 obtain ⟨d,w,L⟩:=chargeMirror P a c μ l X hδ Z.aP A (ν:=r∘ι) hZ -- w L shape error? ∃ C,∃ d,0 ... ⟨d,w,L⟩ L pair Prop, w d
 filter_upwards [fields P,lantern δ D (underlay P.par) c a P.par mast (by norm_num [mast]) hδ,H 2,H 4,Z.clearFor 1 zero_le_one 2 le_rfl,A,L.2] with s h h' v₁ v₂ v₃ v₄ v₅
 filter_upwards [hZ.eventually v₁, hZ.eventually v₂,g.eventually v₃.1,v₅] with n p₁ p₂ t₀ t₁
 let p:=t₀; let q:=irr P (r (ι n)); let q':=uvv P (r (ι n))
 dsimp only; refine ⟨⟨p⟩,fun v R hR=>?_⟩
 have r₁: (RootBook P.run q q' s).p.B=bₛ s:=p.gears.boot.B
 let κ:=p.gears.boot.threshold -- maybe EQ
 let t₂:=h' (?R? s q q').p R r₁ κ hR
 let t₃:=t₁ v
 let Gaw b:=gaucho P s q q' v X R D t₂ (v₄ _ _ p).1 b (by rw [r₁]; exact tubescape P s _ h.2.2) r₁ t₃.2.2
 obtain ⟨_,_,z₁⟩:= p₁; obtain ⟨_,_,z₂⟩:= p₂
 let W(b:Bool):= filmT P s q q' v δ R (!b)
 let V'(b:Bool):= grove P s q q' (!b)
 let R'(b:Bool):=combo P s q q' v X (!b)
 let t₄:=metricC (underlay P.par) c a; let T₅:= supply δ (underlay P.par) c a (RootBook P.run q q' s).p R
 have vh: 1≤ t₄ := le_add_of_nonneg_right (abs_nonneg _)
 have vz: 1≤ T₅:= le_add_of_nonneg_right (abs_nonneg _)
 constructor
 · intro b
   let l:=Jewel.landQ (side P.run q s) (filmT P s q q' v δ R b) 0 (tube P s)
   exact z₁ (2*tube P s) l R _ _ (plants P.run s q q' (Gaw b) vh vz (abs_nonneg _) t₂.basis t₂.gallery t₂.bonds h.1 (h.2.1 _) hR t₂.hearth)
 let l:=Jewel.landQ (side P.run q s) (W false * W true) 0 (tube P s)
 exact z₂ (2*tube P s) l R _ _ (pruning R' P.run s q q' (V:=V') (fun b=>Gaw (!b)) (zero_le_one.trans vz) (abs_nonneg _) (zero_le_one.trans vh) t₂.basis t₂.gallery t₂.bonds h.1 (h.2.1 _) hR t₂.hearth)
#print axioms collecta
