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
set_option maxHeartbeats 300000
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
-- House.margin.Work Bound sharp.D scale below.
variable {σ o:Cover}{w:ℕ}{B:Finset Cover}
local notation "gζ"=> GrowJ P f s *w
local notation "ρQ"=> fWigQ P f s
private lemma transit (h:f ≤ s)(i:Axis)(z:ℤ) : P.mellow s*(planeQ (GrowJ P f s*w) (fWigQ P f s σ) i z:ℝ)= P.mellow f*(planeQ w σ i z:ℝ):=by
 unfold planeQ fWigQ GrowJ; push_cast; rw [←P.mellow_age f s h] -- tune
 ring
local notation "Mω"=> P.mellow
local notation "Κt"=> XûJ P.par P.width f
abbrev pastureQ (P:Spine)(f:ℕ)(w:ℕ)(σ:Cover)(o:Cover)(x:P.VMark):Prop:= InsetQ w σ o (adventJ P x f) (10*XûJ P.par P.width f)
lemma pipeOffsQ (u:pastureQ P f w σ o x)(p:f≤ s)(v:Holdκ P s f x B):PipeQ P.calibration (GrowJ P f s*w) (fWigQ P f s σ) o B:=by
 intro i y t
 obtain ⟨a,b⟩:= v i y t; obtain ⟨gH,qH⟩:= u i; let h:=P.mellow_good f; have k:= NumberRK P f; let d:=Κt; let U:= planeQ w σ i (o i); let V:=planeQ w σ i (o i+1); let z:=adventJ P x f i
 have h':(U:ℝ)+10*(d:ℝ) ≤ z:=by exact_mod_cast gH
 have e':(z:ℝ)+10*(d:ℝ) ≤ V:=by exact_mod_cast qH
 have l:(10:ℝ)≤d:=by exact_mod_cast k
 have hf:= abs_le.mp (spale_J P x f i); have hp(A:ℤ):= transit (P:=P) (w:=w) (σ:=σ) f s p i A -- tune
 have he: P.mellow f* U ≤ (x i:ℝ)- P.mellow f*d:=by unfold U z at *; linarith only [mul_le_mul_of_nonneg_left l h.le,hf.1,hf.2,mul_le_mul_of_nonneg_left h' h.le]
 have hc : (x i:ℝ)+P.mellow f*d ≤ P.mellow f*V:=by unfold V z at *; linarith only [mul_le_mul_of_nonneg_left l h.le,hf.1,hf.2,mul_le_mul_of_nonneg_left e' h.le]
 constructor
 · have hq:(planeQ gζ (ρQ σ) i (o i):ℝ) ≤ (y i:ℝ)- P.calibration.ℓ:= le_of_mul_le_mul_left (((hp _).trans_le he).trans a) (P.mellow_good _)
   rw [le_sub_iff_add_le] at hq; exact_mod_cast hq
 have hq:(y i:ℝ)+ P.calibration.ℓ ≤ (planeQ gζ (ρQ σ) i (o i+1):ℝ):= le_of_mul_le_mul_left ((b.trans hc).trans_eq (hp _).symm) (P.mellow_good _)
 exact_mod_cast hq
lemma cautiousQ (v:InsetQ w σ o (adventJ P x f) (cautionQ P f)):pastureQ P f w σ o x:=by
 intro i; have ht:= v i; unfold cautionQ at ht; omega
lemma commonQ (y:P.VMark)(p:pastureQ P f w σ o x)(t:pastureQ P f w σ o y)(i:Axis): |(x i:ℝ)-(y i:ℝ)|≤P.mellow f*w:=by
 let d:=Κt; have u(z:P.VMark)(p:pastureQ P f w σ o z): P.mellow f*(planeQ w σ i (o i):ℝ) ≤ (z i:ℝ)∧(z i:ℝ)≤ P.mellow f*(planeQ w σ i (o i+1):ℝ):=by
    obtain ⟨b,v⟩:=p i
    have he:(planeQ w σ i (o i):ℝ)+10*(d:ℝ)≤ adventJ P z f i:=by exact_mod_cast b
    have hq:(adventJ P z f i:ℝ)+10*(d:ℝ) ≤ planeQ w σ i (o i+1):=by exact_mod_cast v
    have h:=abs_le.mp (spale_J P z f i); have hk:=P.mellow_good f; have hl:(10:ℝ)≤d:=by exact_mod_cast NumberRK P f
    constructor <;> linarith only [mul_le_mul_of_nonneg_left he hk.le,mul_le_mul_of_nonneg_left hq hk.le,mul_le_mul_of_nonneg_left hl hk.le,h.1,h.2]
 obtain ⟨h,z⟩:=u x p; obtain ⟨hv,u⟩:=u y t; rw[abs_le]; unfold planeQ at *; push_cast at *; constructor <;> linarith
-- Π Wallet for any n.o from uniqueness
local notation "T"=> P.run
open BoonsθJ SlabMark SlabMark.Etch BProof BProof.PricePort Gleam Gleam.clocks Py.Rate Py.Rate.LocalLimit
lemma SiteQP {j n:Side}{k:ℕ}(p:PortsideQ j n w)(h:k=(2*n.val)^4): sites j ≤ ((w^4:ℕ):ℝ)*k:=by
 unfold sites; have ht:(More j).val=w*(2*n.val):=by change j.val*2=_; rw[p.2]; ring
 rw [ht,Nat.cast_mul,mul_pow,h]; push_cast; exact le_rfl -- tune sites
abbrev TaxE_Q (P:Spine)(f:ℕ)(w:ℕ):ℝ:=2*Real.exp (5*saveZ (hat P.par.R.L P.par.x f)*(w:ℝ)^4)
lemma pursePQ {n:Side}{r:Side}{k:ℕ} (z: PortsideQ r n w)(p:k=(2*n.val)^4): SkyWJ P.par r f ≤ TaxE_Q P f w^k:=by
 have h:= SiteQP z p; have hn: 1≤ k:=by rw[p]; have t:= n.property; apply Nat.succ_le_of_lt; positivity
 let s:=5*saveZ (hat P.par.R.L P.par.x f)
 let F:= Real.exp (s*(w:ℝ)^4)
 have ht:0≤ s:=mul_nonneg (by norm_num) (coin_pos ..).le; push_cast at h; have hw:1≤F:=Real.one_le_exp (mul_nonneg ht (by positivity))
 change 1+Real.exp (s*sites r)≤(2*F)^k; rw[mul_pow]; have hx: Real.exp (s*sites r)≤ F^k:=by unfold F; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_left h ht]
 have ht: (1:ℝ)≤ F^k:=one_le_pow₀ hw; have he: (2:ℝ)≤2^k:=le_self_pow₀ (by norm_num) (by omega); linarith only [hx,ht,mul_le_mul_of_nonneg_right he (zero_le_one.trans ht)]
abbrev CouncilQ(P:Spine)(m:ℕ):ℕ:= (AgateQ P).val*(m+1)*P.par.R.L.val
lemma chordCarryQ: WoodQ P f m ≤ CouncilQ P m* WorkWJ P f:=by
 apply (WoodCeilQ P f m).trans; have ht: chordQ P f≤ WorkWJ P f:=by unfold chordQ cautionQ WorkWJ; have h:= NumberRK P f; omega
 apply le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht))); unfold CouncilQ; exact le_of_eq (by ring)
lemma WharfScaleQ (m:ℕ): ∃ t:ℝ,0<t∧∀ f:ℕ, TaxE_Q P f (WoodQ P f m) ≤ t:=by
 let c:=CouncilQ P m; let K(x:ℝ):=5*saveZ x*((c:ℝ)* WProgJ P x)^4
 have h: Tendsto K atTop (𝓝 0):= ((show RunRate (-gratuity/2) 0 (fun i:ℝ=>5*saveZ i) from (RunRate.coins ..).cmul _).mul (show RunRate 0 0 (fun x:ℝ=>((c:ℝ)*WProgJ P x)^4) from by simpa using (((FiatHighJ P).cmul (c:ℝ)).pow 4))).tends (Or.inl (by norm_num [gratuity]))
 have ht:Tendsto (fun f=>Real.exp (K (hat P.par.R.L P.par.x f))) atTop (𝓝 1):=by simpa only [Function.comp_def,Real.exp_zero] using (Real.continuous_exp.continuousAt.tendsto.comp (h.comp (Py.Rate.LocalLimit.turnover P.par)))
 obtain ⟨C,v⟩:=ht.bddAbove_range; refine ⟨2* max 1 C,mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left ..)),fun f=>?_⟩
 unfold TaxE_Q; refine mul_le_mul_of_nonneg_left (le_trans ?h ((v (Set.mem_range_self f)).trans (le_max_right ..))) (by norm_num) -- tune
 case h=>
    apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (coin_pos ..).le)
    apply pow_le_pow_left₀ (by positivity) _; exact_mod_cast chordCarryQ P f m
abbrev FootPQ (P:Spine)(f m:ℕ):ℝ:=P.mellow f* WoodQ P f m
lemma FStampQ (u:ℝ)(h:0≤ u)(v:u < (P.par.R.L.val:ℝ)):Tendsto (fun f:ℕ=>FootPQ P f m*u^f) atTop (𝓝 0):=by
 let t:=CouncilQ P m; have hz:Tendsto (fun f:ℕ=>↑t*(PlethoraJ P f*u^f)) atTop (𝓝 0):=by simpa using ((PetitionJ (P:=P) u h v).const_mul (t:ℝ))
 refine squeeze_zero_norm' (Eventually.of_forall fun i=>?_ ) hz; change ‖FootPQ P i m * u^ i‖ ≤ t*(PlethoraJ P i*u^i); have h0:= P.mellow_good i; have e:0≤ FootPQ P i m:=mul_nonneg h0.le (Nat.cast_nonneg _)
 rw[Real.norm_eq_abs,abs_of_nonneg (mul_nonneg e (pow_nonneg h _)),←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg h _)
 unfold FootPQ PlethoraJ; rw[mellow_firm,mul_left_comm (t:ℝ)]; apply mul_le_mul_of_nonneg_left _ h0.le
 have h:WoodQ P i m≤ t* WorkWJ P i:=chordCarryQ P i m
 have hp:(1:ℝ)≤ (ruler P.par.block:ℝ):=by exact_mod_cast ruler_gene P.par.block -- tune types
 rw [Int.cast_mul,Int.cast_natCast]; apply le_trans (by exact_mod_cast h : (WoodQ P i m:ℝ) ≤ (↑(t*WorkWJ P i):ℝ)); rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Nat.cast_nonneg _) hp) (Nat.cast_nonneg _) -- tune
#print axioms WharfScaleQ
#print axioms FStampQ
#print axioms pipeOffsQ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
