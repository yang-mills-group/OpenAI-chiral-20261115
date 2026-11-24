import GaugeFieldConstruction.TabMosaicQ
import GaugeFieldConstruction.BayburtQ
import GaugeFieldConstruction.CarillonQ
import GaugeFieldConstruction.HighlightQ
import GaugeFieldConstruction.PalisadeQ
import GaugeFieldConstruction.StevanjaJ
import GaugeFieldConstruction.SakhaJ
import GaugeFieldConstruction.VoletyJ
import GaugeFieldConstruction.LayGateQ
import GaugeFieldConstruction.HitachiQ
import GaugeFieldConstruction.DresdenJ
import GaugeFieldConstruction.FrayTideJ
import GaugeFieldConstruction.SteepleJ
import GaugeFieldConstruction.MovingH
import GaugeFieldConstruction.ZagoraJ
import GaugeFieldConstruction.VirenneJ
import GaugeFieldConstruction.TrollopJ
import GaugeFieldConstruction.ZucatoJ
import GaugeFieldConstruction.KronenJ
import GaugeFieldConstruction.MapicoJ
import GaugeFieldConstruction.LongBowJ
import GaugeFieldConstruction.OrigamiJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.TuristaJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.Limbra3
import GaugeFieldConstruction.AshtonM
import GaugeFieldConstruction.Accomplished
import GaugeFieldConstruction.Kabul
import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Garlic
import GaugeFieldConstruction.Ochre
import GaugeFieldConstruction.Coral
import GaugeFieldConstruction.Dales
import GaugeFieldConstruction.Harries
set_option autoImplicit false
set_option maxHeartbeats 78000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
variable (P:Spine) {X:Type}[Fintype X][LinearOrder X]
open ProbeθJ Preparation Yoke
-- Pose. Film any from Advent plus f mirrors. only valid Stamps.S.
local notation "KΑ"=>P.calibration
local notation "Kγ"=>P.par
local notation "Lγ"=> P.par.R.L
local notation "ℓν"=>P.par.R.L.val
local notation "HΥ"=> inkΛJ
variable (x:P.VMark) (f s:ℕ) (j:Axis)
open Etch
local notation "zA" s:max=> GrowJ P f s
local notation "κs"=> (GrowJ P f s:ℤ)
local notation "W_η"=> WorkWJ P f
local notation "ws"=> GrowJ P f s* WorkWJ P f
local notation "Zγ"=>Mapnest P f x
local notation "ΚΩ"=> XûJ P.par P.width f
local notation "Θζ"=> HearthJ P f s x j
local notation "Vg"=> fShiftJ P f j x
local notation "ΕΦ"=> ruler (KΑ).B
local notation "ZΩ" => pet (Mapnest P f x) j 0
local notation "ℓχ" => P.par.R.L.val
open WallsQ
open SlabMark.Weir
variable (m:ℕ)
local notation "Z₁"=> AgateQ P
local notation "ιw"=> WailsQ P f m
local notation "wQ"=> WoodQ P f m
local notation "Vκ"=> chordQ P f
local notation "ζp"=> cautionQ P f
local notation "G'^" M:max=> GrowJ P f s*M
local notation "VΘ"=> fWigQ P f s
local notation "Y£"=> P.run
local notation "κς"=> KΑ
local notation "κφ"=> P.par
-- tested ANY f-quilt at s, explicit lifts
-- visits at f. define Panel.Reader rule that yields all $sharp$s. No support included since pair arcs need separations at s'
open BoonsθJ
open ExpeditionQ
open Etch
local notation "Ao" v:max=> XûJ P.par P.width v
local notation "ρm"=> P.mellow
local notation "Lp"=> P.par.R.L.val
-- choose separation as WorkW scalar h, enough.
def rangePQ (P:Spine)(s:ℕ):ℝ:= P.mellow s* WorkWJ P s
abbrev PriceιQ (P:Spine)(s:ℕ):= 4* WorkWJ P s
lemma RangePosQ :0< rangePQ P s:=by
 have h:P.mellow s>0:=P.mellow_good _; unfold rangePQ; have k:0<WorkWJ P s:=by unfold WorkWJ XûJ; omega
 positivity
open FullBill
open BProof BProof.PricePort
lemma EconomPQ (c:ℝ)(h:0<c): ∀ᶠ s:ℕ in atTop, (WorkWJ P s:ℝ) ≤ c*s:=by
 let V:= P.par; let Υ:= P.par.R.L; let Z:ℝ:=billX Υ; let K:= (1+|Z|)⁻¹*c/2; have v:0<K:=by unfold K; positivity
 have he: ∀ᶠ x:ℝ in atTop,(WProgJ P x:ℝ) ≤ _ := logPrice 0 0 (FiatHighJ P) (c:=1) (d:=0) (w:=0) (v:=K) (Or.inl zero_lt_one) v
 have p': ∀ᶠ s:ℕ in atTop,V.x ≤ ↑s*(1+ |Z|):= by
    have h:Tendsto (fun s:ℕ=> (1+|Z|)*(s:ℝ)) atTop atTop:= Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
    simpa [mul_comm] using h.eventually_ge_atTop V.x
 filter_upwards [(turnover V).eventually he,(turnover V).eventually_gt_atTop 0,p'] with s h0 g p
 rw [coinY g] at h0; apply le_trans h0
 change K*(V.x + _ * _) ≤ _; have he:Z ≤ |Z|:= le_abs_self _; refine le_trans (mul_le_mul_of_nonneg_left (show hat P.par.R.L P.par.x s ≤ (s:ℝ)*(2*(1+ |Z|)) from ?_) v.le) ?_
 · unfold hat; nlinarith [V.R.coarse]
 apply le_of_eq; unfold K; field_simp [show (1:ℝ)+|Z|≠0 from (by positivity)]
lemma DuetLateQ : ∀ᶠ s:ℕ in atTop, PriceιQ P s+20* XûJ P.par P.width s≤ DuoJ P.par P.width f s:=by
 let Z:= XûJ P.par P.width f; have hp:0< Z:=by unfold Z XûJ; omega
 have hLp:1<Lp:=lt_of_lt_of_le (by decide : 1<3) P.par.R.coarse
 let x:= (Lp:ℝ); have hx:1<x:=by unfold x; exact_mod_cast hLp
 have pG:∀ᶠ s:ℕ in atTop, 6*(s:ℝ)*x^f ≤ x^s:=by
    have hv:Tendsto (fun s:ℕ=>6*s*x^f * (x⁻¹)^s) atTop (𝓝 0):=by
       have hx: |x⁻¹|< 1 :=by rw [abs_of_nonneg (by positivity)]; exact inv_lt_one_of_one_lt₀ hx
       have u :=(tendsto_self_mul_const_pow_of_abs_lt_one hx).const_mul (6*x^f)
       rw[mul_zero] at u; exact u.congr (fun i=>by ring)
    filter_upwards [hv.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1))] with i q
    have hx:6*(i:ℝ)*x^f / x^i ≤1:= by rwa[inv_pow,←div_eq_mul_inv] at q
    exact (div_le_one (by positivity)).mp hx
 filter_upwards [pG,EconomPQ P 1 one_pos,eventually_ge_atTop f] with s q v h; rw [one_mul] at v; change ↑(WorkWJ P s) ≤ (s:ℝ) at v; have hv: WorkWJ P s≤ s:=by exact_mod_cast v
 apply le_trans (b:= Lp^(s-f)) ?_ (show Lp^(s-f)≤ _ from le_mul_of_one_le_right (Nat.zero_le _) hp)
 have he: 6*s≤Lp^(s-f):=by
    have u: 6*s* Lp^f≤ Lp^s:=by unfold x at q; exact_mod_cast q
    rw[show Lp^s=Lp^(s-f)*Lp^f from (by rw [←pow_add,Nat.sub_add_cancel h])] at u; exact Nat.le_of_mul_le_mul_right u (pow_pos P.par.R.L.property _)
 unfold PriceιQ WorkWJ at *; omega -- tune unfolded Work inside hcomplex but ok
lemma RangeLowQ : 1/(2*(Lp:ℝ)^s) ≤ rangePQ P s:=by
 unfold rangePQ; rw[ P.mellow_clock]; have he:1 ≤ WorkWJ P s:=by unfold WorkWJ XûJ; omega
 exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast he)
lemma RangeLateQ (u:ℝ)(p:0≤ u)(v:u<(Lp:ℝ)): Tendsto (fun s:ℕ=> rangePQ P s*u^s) atTop (𝓝 0):=by
 apply squeeze_zero_norm' _ (FStampQ P 2 u p v); filter_upwards with i; rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (RangePosQ P i).le (pow_nonneg p _))]; unfold rangePQ FootPQ; apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (P.mellow_good _).le) (pow_nonneg p _); -- need Wood≥Work. chordQ= c=60*X versus Work=100. for m=2.
 have hp:= WoodFloorQ P i 2; have w:1≤ (AgateQ P).val:=(AgateQ P).property; exact_mod_cast (le_trans (show WorkWJ P i ≤ P.par.R.L.val^WailsQ P i 2 from (by unfold WorkWJ; refine le_trans ?_ hp; unfold chordQ cautionQ; omega)) (Nat.le_mul_of_pos_left _ w))
section
variable (Z:Bool→P.VMark)
abbrev RingPQ (P:Spine)(s:ℕ)(Y:Bool→Axis→ℝ):Prop:= (∀ i:Axis, |Y true i-Y false i| ≤3*rangePQ P s)∧∃ i:Axis, rangePQ P s/2≤|Y true i-Y false i|
abbrev TattooQ (P:Spine)(s:ℕ)(Z:Bool→P.VMark):Prop:= RingPQ P s (fun b x=>(Z b x:ℝ))
lemma walkEQ : ∀ᶠ s in atTop,∀ Z:Bool→P.VMark,TattooQ P s Z→∀ᶠ i:ℕ in atTop,∀ k:ℕ, s< P.run.uv k→ CratonQ P f s Z i k (PriceιQ P s):=by
 let V:=P.par; let T:=V.R; let M:=Lp
 filter_upwards [(turnover V).eventually ((@Work.E01.radiusB_tendsto).eventually_ge_atTop (M+10)), DuetLateQ P f] with s q v Z h
 obtain ⟨w,x,d⟩:=h; let U:= adventJ P (Z true) s; let A:=adventJ P (Z false) s; let a:=(Ao s); let W:= WorkWJ P s; let J:= (EtaΘ V s); let L:= PriceιQ P s; have pV:0<P.mellow s:= P.mellow_good s
 let y:Bool→ Axis→ℝ:= fun b x=>(Z b x:ℝ);
 have ppx(i:Axis): |(U i:ℝ)-A i|≤L:=by
    have hu:= spale_J P (Z true) s i; have ht:= spale_J P (Z false) s i; obtain ⟨c,e⟩:= abs_le.mp hu; obtain ⟨f,g⟩:=abs_le.mp ht; obtain ⟨r,t⟩:=abs_le.mp (w i); have hX:2 ≤ W:=by unfold W WorkWJ XûJ; omega
    have hx:(2:ℝ) ≤↑W:=by exact_mod_cast hX
    have he:rangePQ P s=P.mellow s*W:=rfl; rw [he] at r t; apply abs_le.mpr; rw [show (L:ℝ)=4*(W:ℝ) from (by exact_mod_cast (show L=4*W from rfl))]; unfold U A W at *; constructor <;> nlinarith
 have h_X:20*(a:ℝ) ≤ |(U x:ℝ)-A x|:=by
    obtain ⟨e,g⟩:=abs_le.mp (spale_J P (Z false) s x); obtain ⟨b,c⟩:= abs_le.mp (spale_J P (Z true) s x); unfold U A; refine le_abs.mpr ?_; have hh:(1:ℕ)≤a:=by unfold a XûJ; omega
    obtain hq:rangePQ P s=P.mellow s*(100*(a:ℝ)):=by unfold rangePQ WorkWJ a; push_cast; rfl
    rw[hq] at d; rcases le_abs.mp d with h|h; · left; nlinarith [show (1:ℝ)≤ a from (by exact_mod_cast hh)]
    right; nlinarith [show (1:ℝ)≤ a from (by exact_mod_cast hh)]
 have he:J^3 ≤ a:=by unfold a XûJ J V; omega
 have v': M*(4*J+2)+2*J < 20*a:=by
    change M+10 ≤ J at q; have hv:J^2 ≤ J^3:=by gcongr <;> omega
    nlinarith
 filter_upwards [ (goes P.run P.large s).eventually_gt_atTop L ] with i p k t
 let G:=Papal.gram P.run s i k; have ag: G.p.B=J:=(by have hF: G.p=P.run.meter.a s:=(prices_plot P.run s i k t.le).1; rw[hF]; exact (P.run.meter.boot s).2.1)
 let N:= side P.run i s; let b(x:Bool):= SpadeQ P Z s i x;
 have hp:L < N.val:=p -- tune
 have tG: b true-b false=wrap (More N) (U-A):=by rw [map_sub]
 have hv(j:Axis): |(U-A) j| ≤ (L:ℤ):=by change |U j-A j| ≤ _; exact_mod_cast ppx j
 have hy:lift (b true-b false)=U-A:=lift_eq_iff.mpr ⟨tG,fun i=>by change -(↑(N.val*2):ℤ)<_∧_≤(↑(N.val*2):ℤ); obtain ⟨u,v''⟩:=abs_le.mp (hv i); omega ⟩
 have hm:20*a≤ separation (b false) (b true):=by
    rw [separation_comm]; refine le_trans ?_ (component_le _ x)
    rw [hy]; change 20*a≤ (U x-A x).natAbs; have g: ↑(20*a:ℕ)≤ |U x-A x|:=by exact_mod_cast h_X
    rw [←Int.natCast_natAbs] at g; exact_mod_cast g -- need abs
 have ht: separation (b false) (b true) ≤L:=by
    rw[separation_comm]; unfold separation pdist; apply Finset.sup_le; intro i _; rw [hy]; obtain ⟨a,v⟩:=abs_le.mp (hv i); change ((U-A) i).natAbs≤L; omega
 exact ⟨hm,ht, (by rw[show (Papal.gram P.run s i k).p.B=_ from ag]; unfold PriceιQ WorkWJ; unfold a at *; omega), ag.symm ▸ (lt_of_lt_of_le v' hm), v⟩ -- tune ag
-- x+y keeps pasture when x has caution & width. also separation legal.F.Open.
lemma SecondCq (Zs:ℕ) :∀ᶠ s in atTop,∀ Z:Bool→P.VMark,TattooQ P s Z→∀ (σ o:Cover), InsetQ (WoodQ P f m) σ o (adventJ P (Z false) f) (cautionQ P f)→pastureQ P f (WoodQ P f m) σ o (Z true):=by
 have x:1<(Lp:ℝ):= by exact_mod_cast (show 1<Lp from Nat.lt_of_lt_of_le (by decide:1<3) P.par.R.coarse)
 have hp:=RangeLateQ P 1 zero_le_one x; simp only [one_pow,mul_one] at hp
 have e:P.mellow f>0:= P.mellow_good _
 filter_upwards [(hp.eventually (ge_mem_nhds e))] with s v Y h σ o i r
 let k:=Ao f; have hr:1 ≤ k:=by unfold k XûJ; omega
 obtain ⟨u,z⟩:=i r; let V:=mellow P f; let p:=adventJ P (Y true) f r; let c:=adventJ P (Y false) f r; have d : |(p:ℝ)-c|≤ 5:=by
    obtain ⟨y,b⟩:=abs_le.mp (spale_J P (Y true) f r); obtain ⟨w,w'⟩:=abs_le.mp (spale_J P (Y false) f r); obtain ⟨h,z⟩:=abs_le.mp (h.1 r); unfold p c; refine abs_le.mpr ⟨?_,?_⟩<;>nlinarith
 have h: |p-c|≤ (5:ℤ):=by exact_mod_cast d
 unfold cautionQ at u z; obtain ⟨hu,hw⟩:=abs_le.mp h; unfold p c k at *; omega
#check goes
#print axioms walkEQ
#print axioms SecondCq
end
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
