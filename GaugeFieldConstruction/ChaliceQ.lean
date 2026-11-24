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
abbrev PlaneXQ (X:Type)[Fintype X][LinearOrder X](D:X→P.VMark)(W:X→LaurelJ)(L:X→Signed × Bool)(b:BoardDate X)(s:ℕ): PlanBJ P.run i (TolJ X θ):=NeonJ P.run i k P.large θ b (SailRoute P s D W) (incA θ (fun x=> KnitBJ P.par s (W x) (L x)) A) (incG θ M) 0
variable (w:ScarJ P.run i X (Strideθ P.run i (SailRoute P f D W)) f)(e:3*f ≤P.run.uv k)(a:f0 ≤ f)
include w Hw e a
local notation "X_σ"=> (TolHouseJ (X:=X) θ)
local notation "ηρ"=> TwineθJ P.run i X (Strideθ P.run i (SailRoute P f D W)) f
local notation "Zx"=> p.Z i k v g
#check PlaneXQ
lemma CanvassQ :∃ S:PlumberJ P.run i k X θ, SalaryJ p A M i k v g D W R b 0 f S:=by
 have hv:0≤ G:=by obtain ⟨t,h,e,Q⟩:=Hw; exact h.trans ((WindMore _ h).trans e)
 exact p.AtRace v g a (by omega) b _ A M _ _ ⟨FilmRoute _ _ _ _ _ i,w⟩ Hw (fun _=> (show ‖(0:Waves)‖=0 from norm_zero).le.trans hv)
include w e a p
omit Hw
lemma CityCq : RightsBJ P.run i k (TolJ X θ) (PlaneXQ (P:=P) A M i k X D W R b f) f X (TolHouseJ θ) ηρ (fun _=>True):=Phoenix_J P.run i k f P.large θ b (SailRoute P f D W) _ _ 0 (FilmRoute _ _ _ _ _ i) w (fun i g=>p.tempo i (a.trans g)) e (fun _=>True) (fun _ _ _=>trivial) (fun _ _=>rfl) -- tune p issue $p absent include p
omit w e a p
section merge
attribute [-instance] instDecidableEqLex
variable (Z:Bool→P.VMark)(r: X→LaurelJ)(L:Bool→Signed × Bool)(T:BoardDate (ChildQ X))(ι:ℕ)
local notation "Cg"=> ChildQ X
local notation "ξχ"=> (UpperMQ P r f s)
local notation "Yχ"=> (ChildSlotℓ (X:=X) P Z)
local notation "VCH"=> PlaneXQ A M i k (ChildQ X) (Yχ) (UpperMQ P r f s) (L ∘ tip_HQ) T s
local notation "PH"=> PlaneXQ A M i k X (fun _:X=>Z false) r (fun _=> L false) 0 f
local notation "Cp"=> (TolJ X θ)
local notation "D'"=> TolJ (ChildQ X) θ
local notation "Tp"=> SailκJ X θ
local notation "Kp"=> SailκJ (ChildQ X) θ
local notation "zp"=> KernelSailJ (X:=X) (tagHQ false)
local notation "zm"=> OrbitSailJ (X:=X) θ (tagHQ false)
-- parent σ/Embassy exactly.Include. Goal.
open CoeffArc.Directory
open Ione CF.Scree.Ing.Iona
local notation "XT"=> Papal.count P.run s i
variable (gF:f≤ s)(hK:s≤ P.run.uv k)(q':CratonQ P f s Z i k ι)(h':ScarJ P.run i X (Strideθ P.run i (SailRoute P f (fun _:X=>Z false) r)) f)
abbrev ChildMapQ (b:Bool): X→Seat (side P.run i s):=fun x=> Strideθ P.run i (SailRoute P s (ChildSlotℓ (X:=X) P Z) (UpperMQ P r f s)) s (tagHQ b x)
local notation "η"=> ChildMapQ
include gF
lemma PatchKQ (j:Netκ X): (PlaneXQ A M i k Cg (Yχ) (UpperMQ P r f s) (L ∘ tip_HQ) T s).σ s ((KernelSailJ (tagHQ false)) j) = (PlaneXQ A M i k X (fun _:X=>Z false) r (fun _=> L false) 0 f).σ s j := DentonQ _ _ _ _ r _ _ gF le_rfl j.1
lemma TourKQ (j:Netκ X)(x:(TolJ X θ).Pname j):
    (PlaneXQ A M i k Cg (ChildSlotℓ P Z) (UpperMQ P r f s) (L ∘ tip_HQ) T s).tour s ((KernelSailJ (tagHQ false)) j) (nameLift (TolJ X θ) (TolJ Cg θ) (OrbitSailJ θ (tagHQ false)) _ (EmbassyJ_sail θ (tagHQ false)) x) = (PlaneXQ A M i k X (fun _=>Z false) r (fun _=>L false) 0 f).tour s j x:=by
 obtain ⟨d,rfl⟩:=(Facingκ θ j).surjective x; let U:=zp; let C:=(L false); let p:=(VCH); let D:=(PH); let X₀:=U j
 let A₀:=KnitBJ P.par f (r j.1) C; let B:=KnitBJ P.par s (QTapeQ P f s (r j.1)) C; have h:B=A₀:=by unfold B A₀ KnitBJ; rw [(DealQ P f s s gF le_rfl _).1, routeScalarJ _ _]; -- tune
 change sheen B.1 B.2 (A j.2 ((Facingκ θ X₀).symm (Facingκ θ X₀ (show Fin _ from d)))) = sheen A₀.1 A₀.2 (A _ ((Facingκ θ j).symm _)); rw [Equiv.symm_apply_apply,h, Equiv.symm_apply_apply]
omit gF
open CF.Scree.Ing
-- A fuse request stamped at a slot: exactly one Vname output, elected inactive or opening from 0..2 Truth labels.Bounds paid.Flat.Crait
structure ClaimQX (X:Type)(θ:BandS→ℕ) where
  turnOn:X→Bool
  rank:X→BandS
  label(j:X):Fin (θ (rank j))
  lane:X→finsJ
  work:X→List (SailκJ (ChildQ X) θ)
variable (F:ClaimQX X θ)
namespace ClaimQX
abbrev tag (j:X):=Bootκ θ (j,F.rank j) (F.label j) (F.lane j).succ
abbrev Starκ (j:X): SailκJ (ChildQ X) θ:= OrbitSailJ θ (tagHQ false) (F.tag j)
abbrev keys : List (SailκJ (ChildQ X) θ):= ((HallJ X).filter F.turnOn).map F.Starκ
abbrev Fore(x:SailκJ (ChildQ X) θ):X:= bay_HQ (TolHouseJ θ x)
abbrev S_j (x: SailκJ (ChildQ X) θ): List (SailκJ (ChildQ X) θ):= F.work (Fore x)
abbrev FONTQ (j:SailκJ (ChildQ X) θ): Seat (side P.run i s):= ChildMapQ (P:=P) f s i Z r true (Fore j) -- tune
local notation "ωθ"=>FONTQ (P:=P) (θ:=θ) f s i Z r
structure RégisQ :Prop where
   width(x:X): F.turnOn x=true →(F.work x).length ≤ 2
   rate(x:X):F.turnOn x=true→ galaJ (TolHouseJ θ) (F.work x)
   seats(x:X): F.turnOn x=true → ∀ j∈F.work x, Fore j=x
   no(x:X): F.turnOn x=true→ F.Starκ x ∉ F.work x
variable (Pq:RégisQ F)
lemma ant (x:X): Fore (Starκ F x)=x:=rfl
lemma entrance : F.keys.Nodup:= ((sort_nodup ..).filter _).map (fun i j h=> congrArg (@Fore X θ) h) -- tune order
lemma roll (i:SailκJ (ChildQ X) θ): i∈F.keys ↔∃ x,F.turnOn x=true ∧ i=Starκ F x:=by
 constructor
 · intro q; obtain ⟨d,p,t⟩:=List.mem_map.mp q; exact ⟨d,(List.mem_filter.mp p).2,t.symm⟩
 rintro ⟨v,t,rfl⟩; exact List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨(mem_sort ..).mpr (mem_univ _),t⟩,rfl⟩ -- tune hκ
lemma grain (x:SailκJ X θ): TolHouseJ θ (zm x)=labelQ (TolHouseJ θ x) false:=rfl -- syntax
include gF hK q' h' Pq
local notation "Nq"=> Papal.count P.run s i
local notation "ξρ"=> OrbitSailJ (X:=X) θ (tagHQ false)
local notation "σU"=> (TolJ Cg θ).F_v ((VCH).σ s)
local notation "P_f"=> tagHQ (X:=X)
abbrev MintRateQ (ν:ℕ):=Real.exp (-(ν:ℝ))
lemma PontCQ : let DΩ := PlaneXQ A M i k (ChildQ X) (ChildSlotℓ P Z) (UpperMQ P r f s) (L∘tip_HQ) T s; let p':=PlaneXQ A M i k X (fun _:X=>Z false) r (fun _=> L false) 0 f; MergeOpsQ (P_:=TolJ _ θ) (k:=k) s DΩ (TolJ X θ) p' (OrbitSailJ θ (tagHQ false)) (KernelSailJ (tagHQ false)) (FONTQ (P:=P) (θ:=θ) f s i Z r) F.keys (fun _=> MintRateQ ι) F.S_j ∧ QueueOpsQ (P_:=TolJ _ θ) s DΩ (TolHouseJ θ) (OrbitSailJ θ (tagHQ false)) (TolHouseJ θ) (FONTQ (P:=P) (θ:=θ) f s i Z r) F.keys F.S_j :=by
 intro D V; let e:= OrbitSailJ (X:=X) θ (tagHQ false); let Q:=KernelSailJ (X:=X) (tagHQ false)
 let σ:= (TolJ _ θ).F_v (D.σ s); let K:= FONTQ (P:=P) (θ:=θ) f s i Z r; let xR:=TolHouseJ (X:=X) θ; let yR:= TolHouseJ (X:=Cg) θ; let E:=SailRoute P s (ChildSlotℓ (X:=X) P Z) (UpperMQ P r f s); let U:= Strideθ P.run i E; have VQ:= PyxidQ (L:=r) P f s Z i k gF hK ι q' h' -- order
 have h:TolHouseJ (X:=X) θ=xR:=rfl
 have Jπ:= ToniJ P.run i k s s U (FilmRoute P s _ _ _ _) VQ le_rfl hK; have vp:κWork Cg _ yR σ:=fun j k=>⟨fun x=>congrArg (U s) x,fun u=>Jπ u⟩
 have Oc(x:X): σ (Starκ F x)= U s (tagHQ false x):=rfl; have Ωκ(j: SailκJ X θ):σ (OrbitSailJ (X:=X) θ (tagHQ false) j)= U s (tagHQ false (xR j)):=rfl
 have α(i' j:Tp): xR i'=xR j ↔ σ (e i')= σ (e j):=by rw [(vp _ _).symm]; exact ⟨fun g=> congrArg (fun x=>toLex (x,false)) g,fun g=> congrArg bay_HQ g⟩
 have he(i): i∈F.keys →∃ x,F.turnOn x=true∧ i=F.Starκ x:=fun p=>(roll F i).1 p
 have h_Γ(j:SailκJ X θ)(x:X):σ (e j)≠ K (F.Starκ x):=by
    let y:=F.Starκ x; have hz : (tagHQ (X:=X) false (xR j))≠ (tagHQ true x):= fun p=>Bool.noConfusion (congrArg tip_HQ p)
    exact fun v=>hz (Jπ v)
 have ht(x:X):separation (σ (F.Starκ x)) (K (F.Starκ x))= separation (SpadeQ P Z s i false) (SpadeQ P Z s i true):= CupSeQ P f s Z r s i x
 have hx(x:SailκJ (ChildQ X) θ)(p:x∈F.keys): Roots.ψS σ (F.S_j x):=by
    obtain ⟨x,t,rfl⟩:= he x p; exact gala_ψ _ _ yR σ vp _ (Pq.rate x t) -- tune namespace
 have hu(v w)(p:v∈F.keys)(b:w∈F.S_j v):σ w=σ v∨σ w=K v:=by
    obtain ⟨x,t,rfl⟩:=he _ p; have h:=Pq.seats x t w b
    by_cases hv:tip_HQ (TolHouseJ θ w)=false
    · exact Or.inl ((vp _ _).mp (show yR w=toLex (x,false) from (by apply ofLex.injective; exact Prod.ext h hv)))
    exact Or.inr (congrArg (U s) (show yR w=(tagHQ true) x from (by apply ofLex.injective; exact Prod.ext h (Bool.eq_true_of_not_eq_false hv))))
 constructor
 · refine ⟨EmbassyJ_sail θ _, PatchKQ f s A M i k Z r L T gF,TourKQ f s A M i k Z r L T gF,?_,?_, ?_,?_,?_,?_⟩ -- order
   · intro x p; obtain ⟨x,t,rfl⟩:=he _ p; exact decide_eq_false (show (F.lane x).succ ≠0 from Fin.succ_ne_zero _)
   · refine ⟨entrance F,fun i=>?_⟩; apply card_le_one.mpr; intro x p y q
     obtain ⟨r,s⟩:=mem_filter.mp p; obtain ⟨t,d⟩:=mem_filter.mp q; obtain ⟨x,b,rfl⟩:=he _ (List.mem_toFinset.mp r); obtain ⟨y,e,rfl⟩:= he _ (List.mem_toFinset.mp t); exact congrArg F.Starκ (tagHQ (X:=X) false|>.injective (Jπ (s.trans d.symm))) -- tune
   · intro l y; obtain ⟨x,z,rfl⟩:=he _ y; exact ⟨ι,(by exact_mod_cast q'.wage), (by exact_mod_cast (ht x).trans_le q'.price), (Real.exp_pos _).le, le_rfl⟩
   · intro l w; obtain ⟨x,z,rfl⟩:=he _ w; exact q'.space.trans_eq (ht x).symm
   · intro l w; refine ⟨?_,hx _ w,?_⟩
     · obtain ⟨x,p,rfl⟩:=he _ w; exact Pq.width _ p
     intro i p; rcases hu l i w (List.mem_toFinset.mp p) with h|h
     · change σ i∈ insert (σ l) _; rw [h]; exact Finset.mem_insert_self .. 
     exact mem_insert_of_mem (mem_singleton.mpr h)
   intro i h j u t; obtain ⟨x,v,rfl⟩:= he _ h; obtain ⟨z,e,rfl⟩:= he _ u; have hz:z=x:=Pq.seats x v _ t; subst z; exact Pq.no x v t
 refine ⟨⟨hx,fun v p w b=> hu v w p b,fun i p j t=>?_,fun i j a b c=>?_⟩,fun l k t=>?_, fun L v=> (travel_l e σ L).mpr (gala_ψ P.run i xR (σ ∘ e) α L v), ?_⟩ -- queue scope: Gaze outside all keys; realm needs `ψ (l.map e)`. tune
 · obtain ⟨x,v,rfl⟩:=he _ p; obtain ⟨y,z,rfl⟩:=he _ t; exact h_Γ (F.tag y) x
 · obtain ⟨x,v,rfl⟩:=he _ a; obtain ⟨y,w,rfl⟩:=he _ b
   exact fun h=> c (congrArg F.Starκ (tagHQ (X:=X) true|>.injective (Jπ h)))
 · obtain ⟨x,v,rfl⟩:=he _ t; exact h_Γ l x
 have Hp(x:Tp): galaJ yR (RκQ F.keys F.S_j (e x))∧ ∀ a∈RκQ F.keys F.S_j (e x), Fore a=xR x:=by
    unfold RκQ; split_ifs with v -- tune
    · obtain ⟨j,u,h⟩:=he _ v; rw [h]; refine ⟨Pq.rate _ u, fun i v=>?_⟩; exact (Pq.seats j u i v).trans (congrArg (Fore (X:=X) (θ:=θ)) h).symm
    exact ⟨List.pairwise_singleton ..,fun x t=> (List.mem_singleton.mp t) ▸ rfl⟩
 intro l v; unfold HonkQ galaJ at *; rw [List.pairwise_map,List.flatMap_map]; apply List.pairwise_flatMap.mpr
 refine ⟨fun i t=>List.pairwise_map.mp (Hp i).1, (List.pairwise_map.mp v).imp_of_mem ?_⟩
 intro i j p q u x px y py; apply Prod.Lex.lt_iff.mpr; left; change Fore x < Fore y; rw [(Hp i).2 x px,(Hp j).2 y py]; exact u
#print axioms PontCQ
end ClaimQX
end merge
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
