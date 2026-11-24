import GaugeFieldConstruction.Fubini
set_option autoImplicit false
set_option maxHeartbeats 48000
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
variable {A B: Pal}{b c t: Bool}
def salvo(b c:Bool)(X:Pal): Prop:= baseF b*X*baseF c=X
abbrev keyR(g:SU.E):δN:= (1:M2)⊗ₖ Matter.ma g
lemma ship_K (X:Pal): salvo b c (baseF b*X*baseF c):=by unfold salvo; let a:=baseF b; let d:=baseF c; have hp:a*a=a:=(bladeSeal b).1.eq; have hd:d*d=d:=(bladeSeal c).1.eq; change a*(a*X*d)*d= _; simp_rw [←mul_assoc,hp, mul_assoc,hd]; try rfl
lemma ships_r (h:salvo b c A): ∀ a x,(a,x)≠(b,c) → skim_L a x A=0:=by
 intro a x p; rw [←show baseF b*A*baseF c=A from h]; simp_rw [payoff,κHigh]; split_ifs at * <;> simp_all -- see
lemma ships_g (P:Pal) : skim_L b c (baseF b*P*baseF c)= skim_L b c P:=by simp_rw [payoff,κHigh]; cases b <;> cases c <;> simp
lemma ships_c (u: salvo b c A): A=send_L b c (skim_L b c A):=by
 apply θU; intro x p; rw [sendX]; split_ifs with e; · cases Prod.mk.inj e with|intro a f=>subst x p; rfl
 exact ships_r u x p (Ne.symm e)
lemma sendV (S:δN): salvo b c (send_L b c S):=by
 let X:=send_L b c S; let L:= baseF b*X*baseF c; have hp:L=X:=by rw [show L=send_L b c (skim_L b c L) from ships_c (ship_K X)]; unfold L; rw [ships_g]; exact congrArg _ (blank_A ..)
 exact hp
lemma swan (u: salvo b c A)(v: salvo b c B)(q:skim_L b c A=skim_L b c B): A=B:=(ships_c u).trans ((congrArg _ q).trans (ships_c v).symm)
lemma BAs (u:salvo b c A): baseF b*A=A:=by
 let X:=baseF b; let Y:=baseF c; conv=>lhs; rw [← show X*A*Y=A from u]; -- tune rel.D
 change X*(X*A*Y)=A; rw [←mul_assoc,←mul_assoc,show X*X=X from (bladeSeal b).1.eq,u]
lemma BAr (u:salvo b c A):A*baseF c=A:=by
 let X:=baseF b; let Y:=baseF c; conv=>lhs; rw [← show X*A*Y=A from u];
 change X*A*Y*Y=A; rw [mul_assoc,show Y*Y=Y from (bladeSeal c).1.eq,u]
lemma packageV (h:salvo b c A)(u:salvo c t B): salvo b t (A*B)∧ skim_L b t (A*B)= skim_L b c A* skim_L c t B:=by
 refine ⟨?_,?_⟩
 · unfold salvo; rw [← mul_assoc, BAs h,mul_assoc, BAr u]
 rw [payoff]; cases c; · rw [ships_r h b true (by simp),zero_mul,add_zero]; -- tune
 rw [ships_r h b false (by simp),zero_mul,zero_add]
lemma cargoP (g:SU.E)(b c: Bool)(A:Pal): skim_L b c (A*KinX g)=skim_L b c A* keyR g:=by rw [payoff]; simp_rw [KinS]; cases c <;> simp [keyR]
lemma cargoS (g:SU.E)(b c: Bool)(A: Pal): skim_L b c (KinX g*A)=keyR g* skim_L b c A:=by rw [payoff]; simp_rw [KinS]; cases b <;> simp [keyR]
lemma sym_R(h:salvo b c A)(v:salvo b c B)(g:SU.E): A*KinX g= KinX g* B↔ skim_L b c A * keyR g= keyR g* skim_L b c B:=by
 rw [←cargoP, ←cargoS]; refine ⟨congrArg _, fun p=>swan ?_ ?_ p⟩
 · unfold salvo; rw [←mul_assoc, BAs h, mul_assoc,(stake_M _ _).eq.symm, ←mul_assoc,BAr h]
 unfold salvo; rw [←mul_assoc, (stake_M _ _).eq, mul_assoc, BAr v,mul_assoc,BAs v]
lemma neutralX(g:SU.E)(U:M2)(X Y:Op SU.Slot)(p:X * Matter.ma g = Matter.ma g * Y): Commute (1:M2) U ∧ (U⊗ₖ X) * keyR g=keyR g*(U⊗ₖ Y):=by exact ⟨Commute.one_left _, by unfold keyR; rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul,p]⟩ -- tune names
open TableF.Lenten.Loden
def GroundK (b c:Bool): Submodule ℂ Pal where
 carrier:={A|salvo b c A∧∀ g:SU.E,Commute A (KinX g)}
 zero_mem':=⟨by simp [salvo],fun _=>Commute.zero_left _⟩
 add_mem':= by intro i j p q; refine ⟨?_,fun w=>(p.2 w).add_left (q.2 w)⟩; unfold salvo; rw [mul_add,add_mul,p.1,q.1] -- rw p.1 fails under salvo
 smul_mem':=by intro x a p; refine ⟨?_,fun g=>(p.2 g).smul_left x⟩; unfold salvo; rw [Matrix.mul_smul,Matrix.smul_mul,show _=a from p.1] -- tune
lemma SootΘ (A:↥(GroundK b b)): SootK b A.val:=⟨⟨BAs A.property.1,BAr A.property.1⟩,A.property.2⟩
lemma SootΘC (h:SootK b A) : A∈ GroundK b b:=⟨by unfold salvo; rw [h.l,h.r], h.η⟩
lemma GroundV : (GroundK false true)= P03:= by ext1 i; exact ⟨fun p=>⟨p.1,p.2⟩,fun p=>(show SheetQ i from p).casesOn fun u v=>(show i∈GroundK false true from ⟨u,v⟩)⟩
def ΓV(i:Axis):Pal:= Loden.high*gamma_A i*Loden.low
lemma Γχ(i:Axis): salvo false true (ΓV i):=ship_K _
lemma ΓS(i:Axis): skim_L false true (ΓV i)=cliff i ⊗ₖ (1:Op SU.Slot):= ships_g _|>.trans (by unfold gamma_A; rw [leaf,gamma_price]) -- tune implicit
lemma Γκ(i:Axis): ΓV i∈GroundK false true:=⟨Γχ i,fun g=>(sym_R (Γχ i) (Γχ i) g).2 (by rw [ΓS]; exact (neutralX _ _ _ _ (Commute.one_left _).eq).2)⟩
lemma boltL (h:A∈ GroundK b c)(l:B∈ GroundK c t): A*B∈ GroundK b t:=⟨(packageV h.1 l.1).1,fun x=>(h.2 x).mul_left (l.2 x)⟩
lemma Γτ : skim_L false true (ΓV τ)=1:=by rw [ΓS, show cliff τ=1 from (by ext i j; fin_cases i <;> fin_cases j<;>rfl),Matrix.one_kronecker_one]
lemma boltF (A:Pal)(b c t:Bool)(v:A∈ GroundK b c): send_L t t (skim_L b c A)∈ GroundK t t:=by
 let S:=sendV (b:=t) (c:=t) (skim_L b c A); refine (show _ from And.intro S (fun g:SU.E=>(sym_R S S g).2 ?_)); rw [blank_A]; exact (sym_R v.1 v.1 g).1 ((v.2 g).eq)
lemma ΓLeft (A:P03):∃ X:GroundK true true, ΓV τ*X.val=A.val:=by
 have hp:A.val∈GroundK false true:=by rw [GroundV]; exact A.property
 let X:=send_L true true (skim_L false true A.val); let F:=boltF A.val false true true hp
 exact ⟨⟨X,F⟩,swan (packageV (Γχ τ) (show salvo true true X from F.1)).1 hp.1 (by rw [(packageV (Γχ τ) (show salvo true true X from F.1)).2, Γτ,one_mul]; apply blank_A)⟩ -- F.1 syntax inclusion
lemma ΓRight(A:P03):∃ X:GroundK false false,X.val*ΓV τ=A.val:=by
 have hp:A.val∈ GroundK false true:=by rw [GroundV]; exact A.property
 let X:=send_L false false (skim_L false true A.val); let F:=boltF A.val false true false hp; let g:salvo false false X:=F.1
 exact ⟨⟨X,F⟩,swan (packageV g (Γχ τ)).1 hp.1 (by rw [(packageV g (Γχ τ)).2,Γτ,mul_one]; apply blank_A)⟩
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
