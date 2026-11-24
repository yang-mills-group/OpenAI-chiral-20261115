import GaugeFieldConstruction.RankSail
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
variable {x:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male)
abbrev highSea(n:Side)(j:Bool):Finset (Single n):= if j then Tset n else (Tset n)ᶜ
def letters (i:Wa n):Prop:= i.elim True fun ⟨b,i,j⟩=> i∈highSea n b∧j∈ highSea n (!b)∧ i.1.1≠j.1.1
abbrev Tuned(F:Paper n):Prop:=∀ i, F i≠0→ letters i
lemma tuning_h (v:Tuned F) (x:ℂ) : Tuned (x • F):=by intro i p; apply v; intro z; exact p (by simp [z])
lemma tuning_a (v:Tuned F)(u:Tuned H): Tuned (F+H):=by
 intro i p; by_cases h:F i=0; · refine u _ fun z=> p ?_; simp [h,z]
 exact v i h
lemma tuning_sum {I:Type*}(T:Finset I)(F:I→Paper n)(h:∀ i∈T,Tuned (F i)):Tuned (∑ i∈T,F i):=by induction T using Finset.induction_on with|empty=>rw [sum_empty]; exact fun _ v=> (v rfl).elim|@insert i T p ih=>simp only [sum_insert p]; exact tuning_a (h i (mem_insert_self ..)) (ih fun i u=> h i (mem_insert_of_mem u))
lemma tune_s (f: Pane n→ℂ): Tuned (Silex f):=by rintro (_|y) h; trivial; exact (h (by simp [Silex,isolate])).elim
lemma cruiseΘ (U:UNI (Single n))(a b: Finset (Single n))(p:twist U (cutM a)=cutM b)(i j: Single n)(h:U.val i j≠0): i∈ b ↔ j∈a:=by
 have hp: cutM b * U.val=U.val*cutM a:=by rw [← p, twist_product]
 replace hp:= Matrix.ext_iff.mpr hp i j; unfold cutM at hp; by_cases H:i∈b <;>by_cases V:j∈a <;>simp [H,V,h,Ne.symm h] at hp ⊢ -- tune
lemma boost_letters (r:Sweep n)(i j:Wa n)(h:letters i)(u:boostX (launchZ r) (Typer r) i j≠ 0): letters j:=by
 obtain ⟨A,s,t⟩:=r; let L:Sweep n:=⟨A,s,t⟩; rcases j with _|⟨b0,v0,v1⟩; · trivial
 rcases i with _|⟨b,i,j⟩; · exact (u rfl).elim
 have ht(x y: Single n)(p:(launchZ L).val x y ≠ 0): boxA L (aptK x)=aptK y:= Tye.birth_l x y (castX L) _ _ p
 obtain ⟨rfl,e,f⟩:= boost_D _ (Typer L) (boxA L) ht _ _ u; obtain ⟨h0,h1,g⟩:=h
 let r:= Typer L; let U:=launchZ L; have hx(x:Bool): twist U (cutM (highSea n x))=cutM (highSea n (x.xor r)):=by
    have he:=tickR (castX L) (xtra t) (spinU t A) (spinZ t A) n
    change sings t U (cutM _)= swapX r _ at he
    rw [singT,win_cut] at he
    cases x<;>cases hr:r <;> rw [hr] at he 
    all_goals simp only [swapX] at he; simp [highSea,he,dim_cut] -- simp at * too much
 have H:v0.1.1≠v1.1.1:=by intro p; exact g (Tenant.needle (e.symm.trans ((congrArg (fun x=> boxA L (node x)) p).trans f)))
 have hv:moko U r b v0 i*moko U r (!b) v1 j≠0:=by
    change (if b.xor r = b.xor r then moko U r b v0 i*moko U r (!b) v1 j else 0) ≠ 0 at u; simpa using u
 have hk:= left_ne_zero_of_mul hv; have hc:=right_ne_zero_of_mul hv; exact ⟨(cruiseΘ U _ _ (hx b) v0 i (fun p=> hk (mk_s_zero _ _ U v0 i p))).2 h0, (show v1∈ highSea n (!(b.xor r)) from by rw [show (!(b.xor r))=(!b).xor r by cases b <;> cases r <;> simp]; exact (cruiseΘ U _ _ (hx (!b)) v1 j (fun p=>hc (mk_s_zero _ _ U v1 j p))).2 h1),H⟩
lemma Tune_s (r:Sweep n)(p:Tuned F): Tuned (Barber r F):=by
 intro i h; by_contra! k; apply h; funext U; unfold Barber CardCraft; rw [stripeQ]; apply sum_eq_zero; intro j _; by_cases t:F j=0
 · have he :αLines F (flashA r⁻¹ U) j=0:= congrFun t _ -- tune meta
   change _*cSignX _ _=_; rw [he]; simp [cSignX]
 rw [show boostX (launchZ r) (Typer r) j i=0 from Classical.byContradiction fun u=> k (boost_letters r j i (p j t) u), zero_mul]
open scoped Kronecker
abbrev leadB: Finset Hove.Kt:=univ.filter (fun i=> i.1∈plusHalf)
lemma leadHigh : cutM leadB=baseF false:=by
 change cutM leadB=Aop ⊗ₖ (1:Op SU.Slot); rw [← show cutM Lat.plusHalf=Aop from raising.trans Adef.symm]; ext ⟨i,j⟩ ⟨k,l⟩; by_cases h:i=k <;> by_cases p:j=l<;>simp [leadB,cutM,h,p] -- tune
lemma leadLo: baseF true=cutM (leadBᶜ):=by change 1-baseF false =_; rw [←leadHigh]; ext i j; by_cases p:i=j <;> by_cases u:j.1∈plusHalf <;>simp [cutM,p,u]
lemma χbar (F:Pal)(u:baseF false * F *baseF true= F)(i j:Hove.Kt)(h:F i j ≠0) : i.1∈plusHalf∧j.1∉plusHalf:=by
 rw [←leadHigh,leadLo] at u; have he:= Matrix.ext_iff.mpr u i j; unfold cutM at he; simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at he; by_contra! k; by_cases w:i.1∈plusHalf; · simp [leadB,w,k w,Ne.symm h] at he
 simp [leadB,w,Ne.symm h] at he -- tune simp
lemma κv(i:Single n): i∈ Tset n ↔ (portB i).1∈ plusHalf:= mem_Tset ..
lemma tunedΘ (o:Seat n)(i:lotV)(A:Pane n→Pal)(H:KnotK o A)(w:20<n.val) : Tuned (plac (beamer o i A h) true):=by
 rintro (_|⟨b,x,y⟩) p; trivial
 cases b; · exact (p rfl).elim
 have he: ∃ U:Pane n,beamer o i A h U x y≠0:=Classical.byContradiction (fun l=> p (funext fun i=> (not_ne_iff ..).1 (not_exists.mp l i))) -- tune
 obtain ⟨U,B⟩:=he; let V:= keyFare o i h • carryU o i U (A U); have hz:baseF false * V *baseF true=V:= eta_q o i A H U h; change seed_k _ _ V _ _ ≠0 at B; unfold seed_k at B; simp only [Matrix.of_apply] at B; split at B; next t=>
    obtain ⟨c,b⟩:=χbar V hz _ _ B; exact ⟨(κv _).2 c,(show y∈ (Tset n)ᶜ from mem_compl.mpr (fun z=>b ((κv y).1 z))), (fun l=> takes o i w (t.1.trans (l.trans t.2.symm)))⟩
 contradiction
end ArtCart
end MastTin
end YM.CF.XGarden
end
