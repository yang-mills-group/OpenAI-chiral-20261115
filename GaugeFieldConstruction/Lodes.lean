import GaugeFieldConstruction.LampY
import YM.CF.Moto.Road
set_option autoImplicit false
set_option maxRecDepth 4000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 260000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Loden
open Layout HushP ModuleB
variable (A:Pal)(o:Skye.Seat n)(b:Bool)(Y:Pane n→Pal)
variable {A b}
structure SootK (b:Bool)(A:Pal):Prop extends Soot A b where
 η(g:SU.E):Commute A (KinX g)
structure Oneκ (b:Bool)(P:PalOne):Prop where
 β : SootK b P.1
 hr(i): SootK b (P.2.1 i)
def coneκ (b:Bool)(F:yardLot):Prop:=∀ k,SootK b (F k)
lemma nilκ :SootK b 0:=⟨⟨mul_zero _,zero_mul _⟩,fun g=>Commute.zero_left _⟩
lemma Qsm(K:SootK b A)(z:ℂ): SootK b (z • A):=⟨⟨by rw [Matrix.mul_smul, K.l],by rw [Matrix.smul_mul,K.r]⟩,fun i=>(K.η i).smul_left z⟩
lemma coneΚα {B C:Pal}(p:SootK b B)(v:SootK b C): SootK b (B+C):=⟨⟨by rw [mul_add,p.l,v.l],by rw [add_mul,p.r,v.r]⟩,fun i=>(p.η i).add_left (v.η i)⟩ -- tune
lemma coneΚmi {B C: Pal}(p:SootK b B)(v:SootK b C): SootK b (B-C):= ⟨⟨by rw [mul_sub,p.l,v.l],by rw [sub_mul,p.r,v.r]⟩,fun i=>(p.η i).sub_left (v.η i)⟩
lemma coneκsum {I:Type*}{F:I→yardLot}(X:Finset I)(h:∀ i∈X,coneκ b (F i)): coneκ b (∑ i∈X,F i):=by
 induction X using Finset.induction_on with|empty=>rw [sum_empty]; exact fun _=>nilκ|@insert i t p ih=> rw [sum_insert p]; intro k; exact coneΚα (h i (mem_insert_self ..) k) ((ih fun j l=> h j (mem_insert_of_mem l)) k)
lemma coneκn (i:lotV)(v:SootK b A):coneκ b (ηZ A i):=by
 intro k; simp only [ηZ,Pi.single_apply]; split; exact v; exact nilκ
variable {F:yardLot}
lemma coneκC (P:coneκ b F):Oneκ b (comV o F):=by
 have he(S:lotV→ℂ)(X:Finset lotV): SootK b (∑ i∈X,S i • F i):=by induction X using Finset.induction_on with|empty=>rw [sum_empty]; exact nilκ| @insert i X p ih=>rw [sum_insert p]; exact coneΚα (Qsm (P i) _) ih
 constructor
 · rw [stamp_f0]; have ht:=he (fun i=>1) univ; simpa only [one_smul] using ht
 intro i; rw [stamp_f1]; exact he _ _
-- bounded preimages
abbrev fuzzP (P:PalOne):PalOne:= oSub P (comV o (Ωlane P))
def excels (P:PalOne): yardLot:= Ωlane P+ Ωleg (fuzzP o P)
lemma fuzz_A(P:PalOne)(U:Oneκ b P) : Oneκ b (fuzzP o P):=by
 have he:=coneκC o (F:=Ωlane P) (coneκn _ U.β); exact ⟨coneΚmi U.β he.β, fun i=>coneΚmi (U.hr i) (he.hr i)⟩
lemma excels_H(P:PalOne)(U:Oneκ b P):coneκ b (excels o P):=by
 let L:=Ωlane P; let T:=fuzzP o P; have he:Oneκ b T:=fuzz_A o _ U;
 have hp:coneκ b (Ωleg T):=coneκsum univ (fun (i:slice) _ k=> coneΚmi (coneκn (some i,none) (Qsm (he.hr (voltS i)) _) k) (coneκn neutralK (Qsm (he.hr (voltS i)) _) k)) -- placeholder
 exact fun k=> coneΚα (coneκn neutralK (U.β) k) (hp k)
lemma excels_p(P:PalOne)(u:20<n.val)(z:h ≠ 0): let V:=markJet o (notesK o (excels o P) h) h; V.1=P.1∧ V.2.1=P.2.1:=by
 rw [stamps o _ z]; let X:=Ωlane P; let d:=comV o X; let Z:=fuzzP o P
 have he: d.1=P.1:=by unfold d; rw [stamp_f0]; unfold X Ωlane ηZ; simp [Pi.single_apply]
 intro T; change (comV o (X+Ωleg Z)).1=P.1∧ (comV o (X+Ωleg Z)).2.1=P.2.1; rw [comV_add]; constructor
 · change d.1+(comV o _).1=P.1; rw [(pledge₀ (o:=o) Z u).1,he,add_zero]
 apply ContinuousLinearMap.ext; intro i; change d.2.1 i+(comV o _).2.1 i=P.2.1 i; rw [(pledge₁ Z u i).1]; change _+(P.2.1 i-d.2.1 i)=_; abel
abbrev pentCost:ℝ:= 1+legP*(1+(Fintype.card lotV:ℝ)*48^2)
lemma excels_C(P:PalOne)(u:20<n.val): fena (excels o P)≤pentCost*CostOle P:=by
 let L:=Ωlane P; let Z:=fuzzP o P; let c:= (Fintype.card lotV:ℝ)*48^2; let d:= CostOle P
 have he: CostOle Z≤ (1+c)* d:=by
    let hip: fena L ≤ d:=read_Z P; have hp:CostOle (comV o L) ≤ c*d:= (notes_d o L u).trans (le_trans (by apply le_of_eq; show _=c*fena L; unfold c; ring) (mul_le_mul_of_nonneg_left hip (by unfold c; positivity))) -- arg order upperbound ambiguous
    apply (polV_sub ..).trans; apply (add_le_add (a:=d) le_rfl hp).trans_eq; ring
 have hp:fena (Ωleg Z)≤ legP*((1+c)*d):= le_trans (((leg_Z Z).trans_eq (show _=legP*CostOle Z from (mul_assoc ..).symm))) (mul_le_mul_of_nonneg_left he leg_p)
 apply (norm_add_le L (Ωleg Z)).trans; apply (add_le_add (read_Z P) hp).trans_eq; unfold pentCost c d; ring
-- realize Meta through stencil
variable (k:lotV)(A)
lemma tributeK {A:Pane n→Pal}(s:∀ V:Pane n,∀ g:Skye.Seat n→SU.E, A (Lattice.gauge g V) = KinX (g o) * A V * star (KinX (g o)))(V: Pane n)(g:Skye.Seat n→SU.E) : carryU o k (Lattice.gauge g V) (A (Lattice.gauge g V))= KinX (g (node (landX o k))) * carryU o k V (A V)* star (KinX (g (node (landY o k)))):=by
 let R:=KinX (g o); let X:=KinX (g (node (landX o k))); let Y:=KinX (g (node (landY o k))); let B:=A V; let H:=LedgeK (shoreX k) o V; let K:= LedgeK (shoreY k) o V
 unfold carryU; simp only [LedgeK, comp_apply,tare,s, Kin_mul, Kin_inv, star_mul, star_star]; change X*(star H*star R)*(R*B*star R)*(R*K*star Y) =X*(star H*B*K)*star Y; have ht:star R*R=1:= Kin_R _
 simp only [mul_assoc]; simp_rw [←mul_assoc (star R) R,ht,one_mul]
lemma mark_kin {A:Pane n→Pal}(s:∀ V:Pane n,∀ g:Skye.Seat n→SU.E,A (Lattice.gauge g V)=KinX (g o)*A V* star (KinX (g o)))(V:Pane n)(g:Skye.Seat n→SU.E): twist (tradew n g) (beamer o k A h V)=beamer o k A h (Lattice.gauge g V):=by refine shiftP _ _ _ _ _ ?_; rw [tributeK o k s, Matrix.mul_smul,Matrix.smul_mul] -- tune
lemma soot_b(k:lotV)(P:SootK b A)(V:Pane n):Mott b (beamer o k (fun _=>A) h V):=by
 intro i j; unfold beamer modelK; simp only [star_P]; split_ifs; swap; · exact nilκ.toSoot
 let X:=KinX (TarA o (shoreX k) V)⁻¹; let Z:=KinX (TarA o (shoreY k) V); let f:=carryU o k V A
 have he:f=X*A*Z:=by unfold X Z f carryU LedgeK; rw [Kin_inv]; rfl
 have hp:baseF b*f=f:=by unfold f; rw [show carryU _ _ _ _=_ from he,← mul_assoc,←mul_assoc, (stake_M _ _).eq,mul_assoc X, P.l]
 have hx:f*baseF b=f:=by rw [he, mul_assoc _ Z,(stake_M _ _).eq.symm,← mul_assoc _ _ Z,mul_assoc X, P.r]
 constructor; rw [Matrix.mul_smul,hp]; rw [Matrix.smul_mul,hx]
end Loden
end Lenten
end YM.CF.TableF
end
