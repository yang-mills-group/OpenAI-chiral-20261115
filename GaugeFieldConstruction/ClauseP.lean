import GaugeFieldConstruction.Quatrain
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
variable {x y:Cover}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h r:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
variable (x n k)
namespace Zpress
section
variable {E:Type}[LinearOrder E][Fintype E] {q Q s t G:ℝ}{S T:Finset E}{l m d:ℕ}{P'D P'F:Fock.FC E}
variable {F V: Fock.FC E}
lemma lift_C (u:pressedF S d q F)(p:q≤ Q) (m:d≤l)(t:S⊆ T): pressedF T l Q F:=by obtain ⟨L,h,t',x⟩:=u; exact ⟨L,fun i p=> ⟨(h i p).1,(h i p).2.1.trans m,fun j v=> t ((h i p).2.2 _ v)⟩, t'.trans p,x⟩
lemma add_C (u:pressedF S d q F)(p:pressedF S d Q V): pressedF S d (q+Q) (F+V):=by
 obtain ⟨l,q,t,rfl⟩:=u; obtain ⟨m,Q,v,rfl⟩:=p; refine ⟨l++m,fun i p=> ?_,?_,by simp [orchestrate]⟩
 · rcases List.mem_append.mp p with p|p; exact q _ p; exact Q _ p
 simp only [meterK,List.map_append,List.sum_append]; exact add_le_add t v
lemma Ø_C : pressedF S m 0 (0:Fock.FC E):=⟨[],nofun,le_rfl,rfl⟩
abbrev σSign (z:ℂ)(x:SignWave E): SignWave E:= (z*x.1,x.2)
lemma ScaleC (u:pressedF S d t F)(z:ℂ): pressedF S d (‖z‖*t) (z • F):=by
 obtain ⟨l,v,Q,rfl⟩:=u; let L(G:List (SignWave E)):=G.map (σSign z); have hp(G:List (SignWave E)):orchestrate (L G)=z • orchestrate G:=by
    induction G with|nil=> simp [L,orchestrate]|cons i G ih=> rw [show orchestrate _=_ from (show orchestrate (L (i::G))=(z*i.1) • rollC RootBay i.2+orchestrate (L G) from rfl),ih,mul_smul,←smul_add]; rfl -- tune
 have hz(G:List (SignWave E)): meterK (L G)=‖z‖ * meterK G:=by induction G with|nil=>simp [meterK,L]|cons i G ih=>change ‖z*i.1‖+_=‖z‖*(‖i.1‖+meterK G); rw [norm_mul,mul_add]; exact congrArg (_+·) ih -- ]] -- tune
 refine ⟨L l,fun i p=> ?_, (hz l).le.trans (mul_le_mul_of_nonneg_left Q (norm_nonneg _)),hp _⟩; obtain ⟨i,u,rfl⟩:=List.mem_map.mp p; exact v i u
lemma sum_C {I:Type}[DecidableEq I](L:Finset I)(F:I→Fock.FC E)(K:I→ℝ)(h:∀ i∈L,pressedF S m (K i) (F i)):pressedF S m (∑ i∈L,K i) (∑ i∈L,F i):=by induction L using Finset.induction_on with|empty=>rw [sum_empty,sum_empty]; exact Ø_C|@insert i L p ih=>rw [sum_insert p,sum_insert p]; exact add_C (h _ (mem_insert_self ..)) (ih fun i p=> h i (mem_insert_of_mem p))
abbrev ponder (x y:SignWave E) : SignWave E:= (x.1*y.1, x.2++y.2)
lemma roll_V (i j:List (Creduct E)): rollC RootBay (i++j)= rollC RootBay i* rollC RootBay j:=by induction i with|nil=> simp [rollC]|cons k i ih=> change _*rollC RootBay (i++j) =(_*rollC RootBay i)*_; rw [ih,mul_assoc]
lemma factor_p (x y:SignWave E): motionF (ponder x y)= motionF x*motionF y:=by unfold motionF; change (_*_) • rollC RootBay (_ ++ _) = _; rw [roll_V,mul_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
def steam (l T:List (SignWave E)):= l.flatMap fun i=>T.map (ponder i)
lemma InK (p:pressedF S m q F): 0 ≤ q:=by obtain ⟨l,h,r,v⟩:=p; exact (List.sum_nonneg (fun i p=>by obtain ⟨i,p,rfl⟩:=List.mem_map.mp p; exact norm_nonneg _)).trans r -- tune
lemma mul_C (u:pressedF S d q F) (p:pressedF S m t V):pressedF S (d+m) (q*t) (F*V):=by
 have hp:= InK p; obtain ⟨L,h,r,rfl⟩:=u; obtain ⟨T,K,b,rfl⟩:= p
 have hx(x:SignWave E)(P: List (SignWave E)):orchestrate (P.map (ponder x))=motionF x * orchestrate P:=by induction P with|nil=> simp [orchestrate]|cons i P ih=>change motionF _+orchestrate (P.map _) = _*(motionF i+orchestrate P); rw [mul_add,factor_p,ih]
 have hs(P: List (SignWave E)):orchestrate (steam P T)= orchestrate P*orchestrate T:=by
    induction P with|nil=>simp [orchestrate,steam]|cons k P ih=>change orchestrate ((T.map (ponder k))++steam P T)=(motionF k+orchestrate P)*_; rw [add_mul,show orchestrate _=_ from (show orchestrate ((T.map _) ++ steam P T)= orchestrate (T.map (ponder k))+orchestrate (steam P T) from (by simp [orchestrate])),hx,ih] -- tune
 have hh(x:SignWave E)(P:List (SignWave E)): meterK (P.map (ponder x))= ‖x.1‖*meterK P:=by induction P with|nil=> simp [meterK]|cons i P ih => change ‖x.1*i.1‖+ meterK (P.map (ponder x)) =_*(‖i.1‖+meterK P); rw [norm_mul,ih,mul_add];
 have hv(P: List (SignWave E)):meterK (steam P T)=meterK P *meterK T:=by
    induction P with|nil=> simp [meterK,steam]|cons k P ih => change meterK (_ ++ steam P T) = (‖k.1‖+_)*_; rw [add_mul, show meterK ((T.map (ponder k)) ++ steam P T) =meterK (T.map (ponder k))+meterK (steam P T) from (by unfold meterK; rw [List.map_append,List.sum_append]), hh, ih]; rfl
 refine ⟨steam L T,fun i w=> ?_,(hv L).le.trans (mul_le_mul r b (List.sum_nonneg (fun i p=>?_)) (InK ⟨L,h,r,rfl⟩)), hs L⟩
 · obtain ⟨i,t,p⟩:= List.mem_flatMap.mp w; obtain ⟨j,u,rfl⟩:= List.mem_map.mp p; obtain ⟨hh,hv,Q⟩:=K j u; obtain ⟨p,w,T⟩:= h i t; unfold ponder; simp only [List.length_append]; exact ⟨p.add hh, add_le_add w hv, fun j p=> (List.mem_append.mp p).elim (T j) (Q j)⟩
 obtain ⟨i,p,rfl⟩:=List.mem_map.mp p; positivity
end
end Zpress
end ArtCart
end MastTin
end YM.CF.XGarden
end
