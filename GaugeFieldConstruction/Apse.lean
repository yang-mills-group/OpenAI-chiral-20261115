import GaugeFieldConstruction.ArchV
set_option autoImplicit false
set_option maxHeartbeats 125000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
-- plen capital: anchor unweighted.White v
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
local instance : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance : Module ℂ ↥G15:= PackS.S.toModule
local instance : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance : Module ℂ ↥G3:= PackG.S.toModule
open Phys Row TableF.Lenten.Loden
open Matter (FlavorIndex)
open Raw Calibration
local instance : AddCommGroup Gκ:= PackH.G.toAddCommGroup
local instance : Module ℂ Gκ:= PackH.S.toModule
abbrev offP(v:Waves):PHPane:=(bV0 v,bV1 v,bV2 v)
abbrev Fikit(v:PHPane)(i:G3)(j:Gκ)(k:G15):Waves:= (v.1,(i,v.2.1),j,v.2.2,k)
lemma Pips(v:Waves): v= Fikit (offP v) (bF4 v) (bF5 v) (bm5 v):=rfl
def offM:PHPane→ₗ[ℂ]Waves:=by
 refine ⟨⟨(fun i=> Fikit i 0 0 0),?_⟩,?_⟩
 · intro i j -- tune via explicit
   exact Prod.ext rfl (Prod.ext (Prod.ext (show (0:↥G3)=0+0 from (zero_add _).symm) rfl) (Prod.ext (show (0:Gκ)=0+0 from (zero_add _).symm) (Prod.ext rfl (show (0:↥G15)=0+0 from (zero_add _).symm))))
 intro x y; exact Prod.ext rfl (Prod.ext (Prod.ext (show (0:↥G3)=x • (0:↥G3) from (smul_zero x).symm) rfl) (Prod.ext (show (0:Gκ)=x • (0:Gκ) from (smul_zero x).symm) (Prod.ext rfl (show (0:↥G15)=x • (0:↥G15) from (smul_zero x).symm))))
-- total V5 μ.Unit orth
abbrev shellP (c:Waves) : Calibration.Shell:= (0,μG (bF4 c)+ μD (bF5 c),symf3 (bV0 c)+(symf4 (bV1 c)+ symf5 (bV2 c)),task_M (bm5 c))
def SpineM:Waves→ₗ[ℂ] Calibration.Shell where
 toFun:=shellP
 map_add' x y:=by
    refine Prod.ext (add_zero _).symm <| Prod.ext ?_ <| Prod.ext ?_ (show task_M (bm5 x+bm5 y)=task_M (bm5 x)+task_M (bm5 y) from map_add ..)
    · change μG (bF4 x+bF4 y)+μD (bF5 x+bF5 y)=μG (bF4 x)+ μD (bF5 x)+(μG (bF4 y)+μD (bF5 y)); rw [map_add,map_add,add_add_add_comm]
    change symf3 (bV0 x+bV0 y)+(symf4 (bV1 x+bV1 y)+symf5 (bV2 x+bV2 y))=_; rw [map_add,map_add,map_add]; rw [add_add_add_comm (symf4 _) _ (symf5 _) (symf5 _),add_add_add_comm (symf3 _)]; rfl
 map_smul' r a:=by
    apply Prod.ext; · exact (smul_zero r).symm
    apply Prod.ext; · change μG (r • bF4 a)+ μD (r • bF5 a)= r • ( μG (bF4 a)+ μD (bF5 a)); rw [map_smul,map_smul,smul_add]
    apply Prod.ext; · change symf3 (r • bV0 a)+(symf4 (r • bV1 a)+ symf5 (r • bV2 a))= r • (symf3 (bV0 a)+(symf4 (bV1 a)+symf5 (bV2 a))); rw [map_smul,map_smul,map_smul,smul_add,smul_add]
    exact map_smul task_M r (bm5 a)
def Floc:= Submodule.span ℂ {v:Waves| Looms v}
-- μ axioms tie GE4 GE5 PH5 Mixed signatures & Projection.
lemma level_x(v:Waves) : (SpineM v).2.1= μG (bF4 v)+ μD (bF5 v):=by unfold SpineM; simp only [shellP, LinearMap.coe_mk,AddHom.coe_mk]
lemma level_w(v:Waves) :(SpineM v).2.2.2= task_M (bm5 v):=by unfold SpineM; simp only [shellP, LinearMap.coe_mk,AddHom.coe_mk]
lemma level_y(v:Waves): graph_f (SpineM v).2.2.1=lineup (offP v):=by unfold SpineM; simp only [shellP,LinearMap.coe_mk, AddHom.coe_mk]; rw [map_add,map_add,←LiftF3,←LiftF4,←LiftF5]; unfold offP; rw [lineupH]
lemma rhythm(p:Waves) : SpineM p=0 ↔ μG (bF4 p)+μD (bF5 p)=0∧ lineup (offP p)=0∧task_M (bm5 p)=0:=by
 let V:=SpineM p
 rw [←level_x p,←level_w p,←level_y p]
 have H(g:Calibration.Shell): g=0 ↔ g.1=0 ∧ g.2.1=0 ∧ graph_f g.2.2.1=0∧g.2.2.2=0:=by -- Ut alias
    constructor
    · intro p; subst g; refine ⟨rfl,rfl,?_,rfl⟩; simp only [Prod.snd_zero, Prod.fst_zero,map_zero]
    rintro ⟨p,v,g',h⟩; refine Prod.ext p (Prod.ext v (Prod.ext ?_ h)); apply ffaith; simp only [Prod.snd_zero,Prod.fst_zero,map_zero,g'] -- def.S arg
 rw [H (SpineM p)]; have ht: V.1=0:= rfl; exact ⟨And.right, fun z=>⟨ht,z⟩⟩
lemma kernG (p:Waves): SpineM p=0 ↔ bF4 p=0∧(∀ i:Gem,∀ j∈ liveD,bF5 p i j=0)∧ offP p∈ Rocker∧ bm5 p=0:=by
 rw [rhythm,GaugeFieldConstruction.Wick.Yacht.Vesper.kinG,(rustles _),task_ker]; exact and_assoc
lemma σRock (p:PHPane)(h:p∈ Rocker) : offM p∈ Floc:=by
 apply Submodule.span_induction (p:=fun x _=>offM x∈ Floc) ?_ ?_ ?_ ?_ h
 · rintro x ⟨b,u,h|⟨j,h⟩⟩ <;> rw [h]
   · let Q:PalOne:= (u.val,0,0); exact Submodule.subset_span (show Looms (offM (dyan (taxW u))) from Or.inr ⟨b,Q,⟨SootΘ u,fun _=>nilκ⟩,pleftW u⟩)
   obtain ⟨K,H,q⟩:=pleftX u j; exact Submodule.subset_span (show Looms _ from Or.inr ⟨b,K,H,q⟩)
 · rw [map_zero]; exact Floc.zero_mem
 · intro i j _ _ v u; rw [map_add]; exact Floc.add_mem v u
 intro i x h v; rw [map_smul]; exact Floc.smul_mem i v
def onD_C : Gκ →ₗ[ℂ] Waves where
 toFun x:= Fikit 0 0 x 0
 map_add' a b:= Prod.ext (show (0:↥P03)=0+0 from (add_zero _).symm) (Prod.ext (show (0:J4)=0+0 from (add_zero _).symm) (Prod.ext rfl (show (0:↥P25 × ↥G15)=0+0 from (add_zero _).symm)))
 map_smul' p a:= Prod.ext (show (0:↥P03)=p • (0:↥P03) from (smul_zero p).symm) (Prod.ext (show (0:J4)=p • (0:J4) from (smul_zero p).symm) (Prod.ext rfl (show (0:↥P25 × ↥G15)=p • (0:↥P25× ↥G15) from (smul_zero p).symm)))
-- G4–5 kernel.
lemma taxic(b:Axis)(W:Wed): E15 b W.toBlade (onD_C (blast b W)):=by
 refine ⟨rfl,rfl,rfl,fun i j=>?_⟩; change kite (blueL W) ((LinearMap.proj b).comp breezeD) i j= _; rw [kite_h, Complex.ofReal_mul, white_D j b]; try rfl
set_option maxHeartbeats 430000 in
lemma QuenchF: LinearMap.ker SpineM=Floc:=by
 refine le_antisymm ?_ ?_
 · intro p H; rw [LinearMap.mem_ker] at H; obtain ⟨q,w,t,h⟩:= (kernG _).1 H; have hp:p= offM (offP p)+ onD_C (bF5 p):=by
      apply Prod.ext
      · change (bV0 p)=(bV0 p)+0; rw [add_zero]
      apply Prod.ext
      · apply Prod.ext; · change bF4 p=0+0; rw [q,add_zero]
        change bV1 p=bV1 p+0; rw [add_zero]
      apply Prod.ext; · change bF5 p=0 + bF5 p; rw [zero_add]
      apply Prod.ext; · change bV2 p=bV2 p+0; rw [add_zero]
      change bm5 p=0+0; rw [h,add_zero]
   rw [hp]; apply Floc.add_mem (σRock _ t); obtain ⟨c,H⟩:=crags (bF5 p) w; rw [H,map_sum]; apply Submodule.sum_mem; intro i _; rw [map_sum]; apply Submodule.sum_mem; intro j _; rw [map_smul]; exact Floc.smul_mem _ (Submodule.subset_span (show Looms _ from Or.inl ⟨_,_, taxic _ _⟩))
 apply Submodule.span_le.mpr; rintro p (⟨x,f,g⟩|⟨b,y,u,h⟩);
 · rw [SetLike.mem_coe,LinearMap.mem_ker]; refine (kernG _).2 ⟨g.1,fun i j t=> ?_,?_,g.mixed⟩
   · rw [g.gauge i j,white_D,show breezeD j=0 from t]; simp
   have ht:offP p=0:=Prod.ext (Subtype.ext (congrArg (fun x:PalOne=> x.1) g.phot)) (Prod.ext (Subtype.ext (congrArg (fun x:PalOne=>x.2.1) g.phot)) (Subtype.ext (congrArg (fun x:PalOne=>x.2.2.val) g.phot))) -- tune
   rw [ht]; exact Rocker.zero_mem
 rw [SetLike.mem_coe, LinearMap.mem_ker]; refine (kernG _).2 ⟨h.gauge4,fun i j _=>?_,?_,h.mixed⟩
 · rw [h.gauge5]; rfl
 obtain ⟨a,r,S,v⟩:= αPeak p y u h; have he: bV0 p=0:= by apply Subtype.ext; cases b; exact (h.landing 0).1; exact (h.landing 0).1
 apply (rustles _).1; rw [offP,lineupH,he,r,v,map_zero,kataP,map_sum]; simp_rw [kataT]; simp
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
