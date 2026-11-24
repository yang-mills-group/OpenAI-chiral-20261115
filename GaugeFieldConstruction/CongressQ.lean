import GaugeFieldConstruction.ChaliceQ
import GaugeFieldConstruction.AromaXQ
import GaugeFieldConstruction.BarwinQ
import GaugeFieldConstruction.McGillQ
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
set_option linter.unusedSectionVars false
set_option maxHeartbeats 65000
variable {P}{θ:BandS→ℕ}{G:ℝ}{f0:ℕ}(p:RosterJ P θ G f0)(A:SωJ θ)(M:JωL θ)(Hw:Adept_T θ A M G)(i k n:ℕ)(v:f0≤ P.run.uv k)(g:(P.run.voyage i).kick≤ k)(D:X→P.VMark)(W:X→LaurelJ)(R:X→Signed× Bool)(b:BoardDate X)
local notation "θZ"=>θ
open ClaimQX
section
variable (F G:ClaimQX X θ)(x:X)
-- only turn, read, work, tag
structure GaffXQ (x:X):Prop where
    turn: F.turnOn x=G.turnOn x
    work: F.work x=G.work x
    tag : F.tag x=G.tag x
variable (Y:X→ClaimQX X θ)
def wholeCL (Y:X→ClaimQX X θ): ClaimQX X θ:=⟨fun i=> (Y i).turnOn i, fun i=>(Y i).rank i,fun i=>(Y i).label i,fun i=>(Y i).lane i,fun i=> (Y i).work i⟩
lemma memberCQ : GaffXQ (Y x) (wholeCL Y) x:=⟨rfl,rfl,rfl⟩
lemma harvestQ (v:∀ x, RégisQ (Y x)): RégisQ (wholeCL Y):= ⟨fun i p=> (v i).width _ p,fun i p=> (v i).rate _ p,fun i p=> (v i).seats _ p,fun i p=> (v i).no _ p⟩
-- patch assembly. simpler List with distinct membership and complement ONE Family layout.App.
end
section
variable {T:Type}[Ring T][Algebra ℂ T](P':T→ Prop)(H:T→ℂ)(L Xq:ℝ)(atom:X→ClaimQX X θ→T→ℝ→ Prop)
inductive Enterprise (x:X) : T →ℝ→Prop
| coin (K:ClaimQX X θ)(y:T)(b:ℝ)(q:P' y)(v:RégisQ K)(ε:∀ R,GaffXQ K R x→ RégisQ R → atom x R y b):Enterprise x y b
| add {w v b c}:Enterprise x w b → Enterprise x v c →Enterprise x (w+v) (b+c)
| scale (z:ℂ){v b}:Enterprise x v b→Enterprise x (z•v) (‖z‖*b)
| lift{v b c}:Enterprise x v b→b≤c→Enterprise x v c
variable (tE:∀ x R v b,atom x R v b→0≤b) (pE:∀v w:T,P' v→P' w →H (v+w)=H v+H w) (uS:∀ (z:ℂ)v,H (z • v)=z • H v)(hp:P' 1)(hE:∀ x y,P' x →P' y→ P' (x*y))(hA:∀ x y,P' x→P' y→P' (x+y))(hS:∀ (z:ℂ)v,P' v→P' (z•v))
include tE pE uS hp hE hA hS
variable (l:List X)(H0:ℝ)
private lemma allowed (x:X)(v:T)(b:ℝ)(w:Enterprise P' atom x v b): 0≤b∧P' v:=by
 induction w with
 | coin K v b e z ε=>exact ⟨tE x K v b (ε K ⟨rfl,rfl,rfl⟩ z),e⟩
 | add u w a b=> exact ⟨add_nonneg a.1 b.1,hA _ _ a.2 b.2⟩
 | lift v b a=> exact ⟨a.1.trans b,a.2⟩
 | scale z v a=>exact ⟨mul_nonneg (norm_nonneg _) a.1,hS _ _ a.2⟩
variable (e: ClaimQX X θ)(rE:RégisQ e)(t:l.Nodup)(h0:0≤ H0) (B:∀ (R:ClaimQX X θ), RégisQ R →∀ (Y:X→T)(Z:X→ℝ), (∀x∈ l, atom x R (Y x) (Z x))→ ‖H ((l.map Y).prod)‖≤ H0*(l.map Z).prod)
-- nested induction prefix.R Maintain occupied.Exp.Pe based ONLY on aunt claims not atom global, earns after completing. atomic.
include rE t h0 B
lemma CurrencyCQ (Y:X→T)(Z:X→ℝ)(q:∀x∈l,Enterprise P' atom x (Y x) (Z x)) : ‖H ((l.map Y).prod)‖≤ H0*(l.map Z).prod:=by
 let ent:=Enterprise P' atom
 let Qw(x:X)(m:T)(b:ℝ):Prop:= P' m ∧ ∃ e:ClaimQX X θ,RégisQ e∧∀R,GaffXQ e R x→RégisQ R→ atom x R m b
 suffices h:∀ (l₂ l': List X),l=l'++l₂ →∀ (F:X→T)(b:X→ℝ), (∀x∈l',Qw x (F x) (b x)) → (∀x∈l₂,Enterprise P' atom x (F x) (b x))→ ‖H ((l.map F).prod)‖≤ H0*(l.map b).prod from h l [] rfl Y Z (by simp) q
 intro l₂; induction l₂ with
 | nil=>
   intro l' u F b p _; rw [List.append_nil] at u; rw [←u] at p
   choose δ hδ using (show ∀ i:X,∃ E:ClaimQX X θ,RégisQ E ∧ (i∈l →∀R,GaffXQ E R i → RégisQ R → atom i R (F i) (b i)) from (fun i=>by by_cases g:i∈l; obtain ⟨e,u,v⟩:= (p i g).2; exact ⟨e,u,fun _=>v⟩; exact ⟨e,rE,fun t=>(g t).elim⟩))
   let Ω:= wholeCL δ; have hΩ:RégisQ Ω:= harvestQ δ fun i=>(hδ i).1; exact B Ω hΩ F b (fun i v=> (hδ i).2 v Ω (memberCQ ..) hΩ)
 | cons i l₂ ih=>
   intro l' u F b v d
   let G:T:= (l'.map F).prod; let W:=(l₂.map F).prod; let τ:=(l'.map b).prod; let u':=(l₂.map b).prod
   have hi: ¬i∈l':=fun p=> (List.nodup_append.mp (show (l'++i::l₂).Nodup from u ▸ t)).2.2 i p i (List.mem_cons_self ..) rfl -- tune
   have hm:i∉l₂:=(List.nodup_cons.mp ((List.nodup_append.mp (u ▸ t)).2.1)).1
   have hP(L:List T)(u:∀x∈L,P' x): P' L.prod:=by
      induction L with|nil=>exact hp|cons i l ih=>exact hE _ _ (u _ (List.mem_cons_self ..)) (ih (fun i p=>u _ (List.mem_cons_of_mem _ p)))
   have hg:P' G:= hP _ (fun j h=>by obtain ⟨x,u,rfl⟩:= List.mem_map.mp h; exact (v x u).1)
   have hw:P' W:= hP _ (fun j h=>by obtain ⟨x,u,rfl⟩:= List.mem_map.mp h; exact (allowed P' H atom tE pE uS hp hE hA hS _ _ _ (d _ (List.mem_cons_of_mem _ u))).2)
   have ht:0≤τ:=List.prod_nonneg (fun j h=>by obtain ⟨x,u,rfl⟩:=List.mem_map.mp h; obtain ⟨p,t,q⟩:= (v x u).2; exact tE _ _ _ _ (q p ⟨rfl,rfl,rfl⟩ t))
   have hu:0≤u':=List.prod_nonneg (fun j h=>by obtain ⟨x,u,rfl⟩:=List.mem_map.mp h; exact (allowed P' H atom tE pE uS hp hE hA hS _ _ _ (d _ (List.mem_cons_of_mem _ u))).1)
   suffices T:∀ x:T,∀ y,Enterprise P' atom i x y→ ‖H (G*(x*W))‖≤H0*(τ*(y*u')) by
       rw [u, List.map_append,List.prod_append,List.map_cons,List.prod_cons,List.map_append,List.prod_append,List.map_cons,List.prod_cons]; exact T _ _ (d _ (List.mem_cons_self ..))
   intro x y t'
   induction t' with
   | @coin K y' b' p e ε=>
     let y:= update F i y'; let q:= update b i b'; have Hα:= ih (l'++[i]) (by simpa using u) y q (fun j x=>(by rcases List.mem_append.mp x with h|h; rw[show y j=F j from update_of_ne (fun x:j=i=>hi (x ▸ h)) _ _, show q j=b j from update_of_ne (fun x:j=i=>hi (x ▸ h)) _ _]; exact v j h; obtain rfl:= List.mem_singleton.mp h; change P' _∧∃ K,_; rw [show y _= _ from update_self .., show q _= _ from update_self ..]; exact ⟨p,K,e,ε⟩)) (fun j x=> (by rw[show y j=F j from update_of_ne (fun g:j=i=>hm (g ▸ x)) _ _,show q j=b j from update_of_ne (fun g:j=i=>hm (g ▸ x)) _ _]; exact d j (List.mem_cons_of_mem _ x)))
     unfold y q at Hα; rw [u,List.map_append,List.map_append,List.prod_append,List.prod_append,List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,update_self,update_self] at Hα
     have he {A:Type}(x:A)(g:X→A)(L:List X)(p:i∉L):L.map (update g i x)=L.map g:=List.map_congr_left (fun j u=> update_of_ne (fun h:j=i=>p (h ▸ u)) _ _)
     rw [he _ _ _ hi,he _ _ _ hi,he _ _ _ hm,he _ _ _ hm] at Hα; exact Hα
   | add A B m n=>
     rw [add_mul,mul_add,pE _ _ (hE _ _ hg (hE _ _ (allowed P' H atom tE pE uS hp hE hA hS _ _ _ A|>.2) hw)) (hE _ _ hg (hE _ _ (allowed P' H atom tE pE uS hp hE hA hS _ _ _ B|>.2) hw))]; exact (norm_add_le ..).trans ((add_le_add m n).trans_eq (by ring))
   | scale z p m=> rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,uS, smul_eq_mul,norm_mul]; exact (mul_le_mul_of_nonneg_left m (norm_nonneg _)).trans_eq (by ring)
   | lift e v a=> exact a.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right v hu) ht) h0)
#print axioms CurrencyCQ
end
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
