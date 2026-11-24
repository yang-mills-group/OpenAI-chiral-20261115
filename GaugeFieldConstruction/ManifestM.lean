import GaugeFieldConstruction.ManifestU
import GaugeFieldConstruction.TopSail
import GaugeFieldConstruction.Pleiad
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap ModuleB Haro Hove Fren Work.F03 Taxi
variable (M:Male)
def thrustA(F:Paper n):hart_X n:=fun A=> sealC (αLines F A) true
abbrev thrustB(F:Paper n):hart_X n:=fun A=> -(sealC (αLines F A) false)ᵀ
abbrev thrust(F:Paper n) := thrustA F + thrustB F
def ocean(F:Paper n): InkD n:=fun i=> pulseH (thrust F i)
lemma bpu(V:Paper n):V=isolate none (V none)+plac (thrustA V) true+plac (thrustB V) false:=by
 funext i x; rcases i with _|⟨c,i,j⟩; · simp [isolate,plac]
 cases c <;> simp [αLines,sealC,plac,thrustA,thrustB,isolate]
lemma bpr(V:Paper n)(A:Pane n):AlphaY V A=hollow (V none A)+pulseH (thrust V A):=by
 nth_rw 1 [bpu V]; rw [Alpha_add,Alpha_add,Pi.add_apply,Pi.add_apply,plac_ℓ,plac_ℓ,thrust,Pi.add_apply,pulse_add,show AlphaY _ _=_ from sill_V (V none) _]; abel -- tune
lemma bpu_T(V:Paper n)(U:Pane n): orbitPH (AlphaY V U)= thrust V U∧ lifeH (AlphaY V) U= V none U:=by
 change _ ∧ Pastry.pane _= _; rw [bpr]; constructor; · rw [plainPlus,hol_l,zero_add,spinW]
 change (panHom _) (_+pulseH _)=_; rw [map_add,show panHom _ _= _ from hullB (V none U),show panHom _ _= _ from pulse_sc .., add_zero] -- ambiguity
abbrev cactusK(n:Side)(x:Cover):Seat n:=wrap (More n) x
lemma penC (w:d<n.val)(i:Cover)(h:i∈cartO x d):stem (cactusK n x) (wrap (More n) i)= i-x:= eq_sub_of_add_eq' (prospect_F h w) -- tune
lemma cart_acc (k:Side)(v:d<n.val)(w:d<k.val)(i: Seat n)(p:i∈knotX x d n) : stem (cactusK k x) (wrap (More k) (prospect x i))=stem (cactusK n x) i:=by rw [penC w _ ((prospect_R i).2 p),prospect]; abel
abbrev φMort (x:Cover):= mort x 24
lemma pFκ (x:Cover)(v:φMort x) (W:100<n.val) (V:100<k.val): pointF (cactusK n x) (hereF n v).1.1=pointF (cactusK k x) (hereF k v).1.1:=by unfold pointF; rw [hereD,hereD, penC (by omega : 24<n.val) _ ((ridge_spec _).1 v.1.property),penC (by omega:24<k.val) _ ((ridge_spec _).1 v.1.property)]
lemma Stem_Cx {a b: Cover}(v:nodeC a∈cartO x 24)(p:nodeC b∈cartO x 24)(w:100<n.val): stem (wrap n a) (wrap n b)=b-a:=by
 unfold stem; apply lift_eq_iff.mpr; refine ⟨(map_sub ..).symm,fun i=> by
    have he:= (cart_spec ..).1 v i; have hp:=(cart_spec ..).1 p i; change ( ((2:ℤ)*a i+1)-(x i)).natAbs≤24 at he; change (((2:ℤ)*b i+1) - (x i)).natAbs≤24 at hp; change _<2*(b i-a i) ∧ 2*(b i-a i)≤ _; omega⟩
lemma wind_diff (a b:Cover): Lifted.winding n a * Rush.wind (wrap n a) (b-a) = Lifted.winding n b:=by
 let N:= n.val; let q:= wrap n b; let x:= wrap n a; let P:=periods n a; let H:=periods n b; let K:=periods n (natural x+(b-a))
 have hv:P+K=H:=by
    apply nsmul_right_injective (M:=Cover) n.property.ne'; change n.val • (P+K)=n.val • H; have he:=infT x (b-a); rw [show x+wrap n (b-a)=wrap n b from (by unfold x; rw [map_sub]; abel)] at he; rw [smul_add]; unfold P K H; unfold x at *; linear_combination (norm:=abel) he + (carrying n a)-(carrying n b)
 change fee P * fee K = fee H; rw [←dues,hv]
lemma payMort (x:Cover)(i j:φMort x) (W:300<n.val): Caller (cactusK n x) (hereF n i).1.1 *Caller (cactusK n x) (hereF n j).1.1= feeV n (some (true,i,j)):=by
 let o:= cactusK n x; have he(u:φMort x):8*separation (AnchorN o) (hereF n u).1.1<n.val:=by
    have hx : separation o (aptK (hereF n u))≤24:=by have ht:=here_Q u (by omega:24<n.val); simpa only [knotX,halo_spec,Finset.mem_singleton, exists_eq_left] using ht
    apply delta_o _ _ (by omega); rw [separation_comm]; change 10*separation o (aptK (hereF n u))<n.val*2; omega
 rw [gold_F _ _ _ (he i) (he j)]; change Rush.wind _ (stem (wrap n i.1.val) (wrap n j.1.val))= Lifted.winding n i.1.val * Lifted.winding n j.1.val
 let q:= Lifted.winding n i.1.val; rw [Stem_Cx (x:=x) ((ridge_spec _).1 i.1.property) ((ridge_spec _).1 j.1.property) (by omega), ←wind_diff (n:=n) i.1.val j.1.val,←mul_assoc,show q*q=1 from fee_one _,one_mul] -- tune
variable {F:Psu x 24}{p:BudgetPoint}{c v h:ℝ}
def BarPhi {x:Cover}{d:ℕ}(i j:mort x d)(F:Psu x d)(V:LinksC):ℂ:= F (some (true,i,j)) V-F (some (false,j,i)) V
lemma thrust_E (V:Pane n)(W: 300<n.val)(i j:φMort x):thrust (pR n F) V (hereF n i) (hereF n j)= feeV n (some (true,i,j)) * BarPhi i j F (onC n V):=by
 let G:= pR n F; have hx(i j)(b:Bool):G (some (b, hereF n i,hereF n j)) V=feeV n (some (b,i,j))* F (some (b,i,j)) (onC n V):= congrFun (pR_K n _ (by omega:24<n.val) (some (b,i,j))) V
 change G (some (true,hereF n i,hereF n j)) V + - (G (some (false,hereF n j,hereF n i)) V) = _; rw [hx i j,hx j i,show feeV n (some (false,j,i))= _ from (show feeV n (some (false,j,i))=feeV n (some (true,i,j)) from mul_comm ..),BarPhi, mul_sub,sub_eq_add_neg]
lemma hill_E(i j:φMort x)(W:300<n.val)(h:ℝ)(V: Pane n):hill_Z (cactusK n x) (thrust (pR n F) V) h (hereF n i) (hereF n j) = (h^2:ℂ) * BarPhi i j F (onC n V):=by unfold hill_Z; rw [mul_assoc _ _ (Caller ..),payMort x i j W, thrust_E V W i j,mul_assoc _ _ (_*_),←mul_assoc (feeV ..),feeV_U,one_mul]
abbrev AnteX (n:Side)(x:Cover)(V:Pane n)(h:ℝ)(u:Views)(i j:φMort x)(F:Psu x 24):Tap.Pal:= flare_one i.2 j.2 (PayS (κviews (cactusK n x) (hereF n i).1.1 (hereF n j).1.1) u * ((h^2:ℂ) * BarPhi i j F (onC n V)))
lemma stream_M (W:300<n.val)(V: Pane n)(u:Views)(h:ℝ): streamF (cactusK n x) (thrust (pR n F) V) h u=∑ i:φMort x,∑ j:φMort x, AnteX n x V h u i j F:=by
 let A:= cactusK n x; let I:=φMort x; -- remove
 let P:= hereF (x:=x) (d:=24) n; let G:= thrust (pR n F); let L (j:yardZ (n:=n)):=flare_one (portB j.1) (portB j.2) (PayS (κviews A j.1.1.1 j.2.1.1) u * hill_Z A (G V) h j.1 j.2)
 let O: (I×I)→yardZ (n:=n):=Prod.map P P; let D:Finset _:= univ.image O; have hx:Injective O:= fun _ _ e=> Prod.ext (hereN 24 (by omega) (congrArg (fun i:yardZ=>i.1) e)) (hereN 24 (by omega) (congrArg (fun i:yardZ=>i.2) e)) -- tune
 change (∑ j,L j)=_; rw [←sum_subset (f:=L) (subset_univ D) (fun j _ p=> ?_)]; swap
 · rcases j with ⟨i,j⟩
   have hh:¬ (aptK i∈ knotX x 24 n ∧ aptK j∈knotX x 24 n):= fun g=>p (by
      obtain ⟨a,t⟩:=here_H i (by omega) g.1; obtain ⟨b,h⟩:=here_H j (by omega) g.2; exact mem_image.mpr ⟨(a,b),mem_univ _,Prod.ext t h⟩)
   let E:= pR n F; have he: G V i j=0:=by
      change E (some (true,i,j)) V + -(E (some (false,j,i)) V)= _; rw [show E _= _ from pR_Z n _ (by omega:24<n.val) (some (true,i,j)) hh, show E _=_ from pR_Z n _ (by omega:24<n.val) (some (false,j,i)) (fun p=>hh ⟨p.2,p.1⟩)]; simp
   unfold L hill_Z; rw [he,mul_zero,mul_zero,map_zero]
 rw [show D=_ from rfl,sum_image hx.injOn, Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; unfold L; rw [show hill_Z A (G V) h (O (i,j)).1 (O (i,j)).2 = _ from hill_E (F:=F) i j W h V]; rfl
end ArtCart
end MastTin
end YM.CF.XGarden
end
