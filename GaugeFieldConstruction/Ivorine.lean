import GaugeFieldConstruction.Spicery
import YM.CF.Roots.Seat
import SatinThinPiers
import YM.CF.Mica.Sleet
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
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
namespace Layout
open scoped YM.CF.Mew
open HushP ModuleB Pastry Flot
namespace Fren
open Skye Levier Scroll Spire Ione
open Lattice
open ProjectorNext.Equivariance (bonds pull_increment roll pulledDirection)
-- Point root always moves by pull. x at old.
variable (s:Sweep n)(R:Signed)
-- internal action on Colors and flux chart
abbrev dyeX(b:Bool): SU.group.Color→ₗᵢ[ℝ] SU.group.Color:=if b then Reef.frolic else LinearIsometry.id
lemma dyeF (V:SU.group.Color)(b:Bool): dyeX b (dyeX b V)=V:=by cases b; rfl; exact Reef.fiz2 _
def amt(i:Axis):ℝ:= if R.flip i then -1 else 1
def gird (v:Gem): Gem:=⟨fun i j=> amt R i*amt R j*v.val (R.perm i) (R.perm j),fun i j=>by dsimp only; rw [mul_comm (amt R j) (amt R i),←mul_add,v.property,mul_zero]⟩
def girdS (v:Sut):Sut:=by
 let F(i j k:Axis):= amt R i*amt R j*amt R k*v.val (R.perm i) (R.perm j) (R.perm k); refine ⟨F,?_,?_⟩
 · intro i j k; unfold F; rw [mul_right_comm (amt R i) (amt R k) (amt R j),←mul_add,v.property.1,mul_zero]
 intro i j k; unfold F;
 rw [show amt R j*amt R k*amt R i=amt R i*amt R j*amt R k from (by ring),show amt R k*amt R i*amt R j=amt R i*amt R j*amt R k from (by ring),←mul_add,←mul_add,v.property.2,mul_zero]
lemma amt_shift (k:Axis):amt R k* amt R k=1:=by cases h:R.flip k<;>simp [amt,h]
lemma amt_rev(k:Axis): amt R⁻¹ (R.perm k)=amt R k:=by simp [amt]
lemma perm_back(k:Axis): R.perm (R⁻¹.perm k)=k:=by simp
lemma perm_for(k:Axis): R⁻¹.perm (R.perm k)=k:=by simp
lemma amt_ρ(k:Axis): amt R⁻¹ k=amt R (R⁻¹.perm k):=by simp [amt]
lemma gird_flip(F: Gem): gird R⁻¹ (gird R F)=F:=by
 apply Subtype.ext; funext i j; change amt R⁻¹ i * amt R⁻¹ j*(amt R _*amt R _*F.val _ _)= _; rw [←amt_ρ,←amt_ρ,perm_back,perm_back]; let a:=amt R⁻¹ i; let b:=amt R⁻¹ j; change a*b*(a*b*F.val i j)= _; rw [show a*b*(a*b*F.val i j)= a*a*(b*b)*F.val i j from by ring,show a*a=1 from amt_shift ..,show b*b=1 from amt_shift ..,one_mul,one_mul]
lemma girdS_rev(F:Sut): girdS R⁻¹ (girdS R F)=F:=by
 apply Subtype.ext; funext i j k; change amt R⁻¹ i*amt R⁻¹ j * amt R⁻¹ k*(amt R _*amt R _* amt R _* F.val _ _ _)= _; rw [←amt_ρ, ←amt_ρ, ←amt_ρ,perm_back,perm_back,perm_back]; let a:=amt R⁻¹ i; let b:=amt R⁻¹ j; let c:=amt R⁻¹ k; let X:= F.val i j k; change a*b*c*(a*b*c*X)=X; rw [show a*b*c*(a*b*c*X)=a*a*(b*b)*(c*c)*X from (by ring),show a*a=1 from amt_shift .., show b*b=1 from amt_shift ..,show c*c=1 from amt_shift ..]; ring
-- weighted edge midpoints. Moving when negative costs endpoint start offset, with true integral uses.
lemma mid_c (F:ComG)(x:Cover)(i:Axis) : formC F i x= (1/2:ℝ) • ∑ j:Axis, lineSi x i j • F.val j i:=by
 unfold formC; rw [Pi.smul_apply]; congr 1; apply sum_congr rfl; intro j _; by_cases p:i=j
 · subst j; simp [fluxZ]
 simp [lineSi,hit,p,Ne.symm p]
lemma mid_s(F:ComT)(x:Cover)(i:Axis):formT F i x=(1/3:ℝ) • ∑ j:Axis,lineSi x i j • ∑ k: Axis,lineSi x i k • F.val k j i:=by
 unfold formT; congr 1; apply sum_congr rfl; intro j _; by_cases p:i=j
 · subst j; simp_rw [F_slot0]; simp
 simp [lineSi,hit,p,Ne.symm p]
-- account.D... x on moved coords from v. need both endpoint near nonwrap. 
abbrev sh (o:Skye.Seat n):= (boxA s).symm o
abbrev feeB := (assembly n).embed s.b
abbrev sent (e: Edge (Skye.Seat n)):= bonds s.s (feeB s) e
def ceilingP (o:Skye.Seat n)(X:Support (More n)): Prop:= Nonwrapping X o
lemma stem_S (i:Skye.Seat n)(v: 10 * separation (boxA s i) o < (More n).val): stem o (boxA s i)=s.s.act (stem (sh s o) i):=by
 have hx: boxA s (sh s o)=o:= Equiv.apply_symm_apply ..
 have ht:10 * separation i (sh s o)< (More n).val:=by rw [←sitT s,hx]; exact v
 apply lift_eq_iff.mpr; refine ⟨?_,fun j=>?_⟩
 · rw [←wrap_signed]; unfold stem; rw [wrap_lift,Signed.act_sub,sitA]; unfold Lattice.affine; have hz:= (sitA s (sh s o)).symm.trans hx; unfold Lattice.affine at hz; linear_combination (norm:=abel) hz
 obtain ⟨k,rfl⟩:= s.s.perm.surjective j; rw [Signed.act_at]; have he:= component_le (i-sh s o) k; unfold stem separation at *; split <;> omega
-- extent qualifier both endpoints. send=(boxA s i,..) or -(aligned edge). stem_S variable for either start. 
lemma fit_spin (e:Edge (Skye.Seat n))(h:fitsSpan (moveHub s X).val.2 e): fitsSpan X.val.2 (sent s e):=by
 let T:=(moveHub s X); let V(e:Edge (Skye.Seat n)):=ProjectorNext.Equivariance.send_mem s.s (feeB s) T.val.2 e
 have hp:=V e|>.mpr h; have he:T.val.2.image (affine s.s (feeB s))= X.val.2:=by
    have v: affine s.s (feeB s)=boxA s:=funext fun x=> (sitA ..).symm; rw [v]; ext i; simp [T,moveHub]; constructor; rintro ⟨a,b,k⟩; exact k ▸ b; intro p; exact ⟨(boxA s).symm i,(by simpa),Equiv.apply_symm_apply ..⟩ -- tune
 rw [he] at hp; exact hp
set_option maxHeartbeats 120000 in
lemma mid_valuation (e: Edge (Skye.Seat n))(v:fitsSpan (moveHub s X).val.2 e)(h:Nonwrapping X.val.2 X.val.1)(t:10 ≤ (More n).val)(k:Axis):
   let Y:=sent s e; lineSi (stem X.val.1 Y.1) Y.2 (s.s.perm k) = amt s.s k*lineSi (stem (moveHub s X).val.1 e.1) e.2 k :=by
 intro Y; have ht: boxA s e.1∈ X.val.2:= (Finset.mem_map_equiv.mp v.1 : _) -- tune
 have hp: 10* separation (boxA s e.1) X.val.1 <(More n).val:= by exact h (boxA s e.1) ht -- orientation
 let R:= s.s; let b:= X.val.1; let x:= stem (sh s b) e.1; let a:=e.2; let V:=stem b (boxA s e.1); have hv:V=R.act x:=stem_S s e.1 hp
 have hy: Y = if s.s.flip e.2 then (boxA s e.1-step (s.s.perm e.2),s.s.perm e.2) else (boxA s e.1,s.s.perm e.2):=by unfold Y sent; rw [ProjectorNext.Equivariance.send_formula, ←sitA]
 by_cases f: R.flip e.2
 · rw [if_pos f] at hy
   have hh:=fit_spin s e v; change fitsSpan X.val.2 Y at hh; rw [hy] at hh; have he: stem X.val.1 Y.1 =V-step (R.perm a):=by
      have h':10*separation Y.1 b <(More n).val:=by rw [hy]; exact h _ hh.1 -- orientation
      have he:= stem_f b Y.1 (R.perm a) h' t; rw [show Y.1+step (R.perm a)=boxA s e.1 from (by rw [hy]; simp [R,a])] at he; exact eq_sub_of_add_eq he.symm
   rw [he,hv]; rw [show Y.2=R.perm a from (by rw [hy])]; change lineSi _ _ (R.perm k)= amt R k*lineSi x _ k; let W:= R.act x; by_cases p:k=a
   · subst k; simp only [lineSi,digit,Pi.sub_apply, R.act_at]; unfold amt; have hx:R.flip a=true:=f; simp [a,hit,f]
     ring -- tune
   cases hp:R.flip k<;> simp [lineSi,digit,hit,R.act_at,amt,p,a,hp,Equiv.injective R.perm|>.eq_iff] -- tune
 rw [if_neg f] at hy; rw [hy]; change lineSi V (R.perm a) _=_; rw [hv]; change lineSi _ (R.perm a) (R.perm k)= amt R k*lineSi x a k; by_cases e:k=a; · subst k; change R.flip a≠true at f; simp [lineSi,digit,hit,amt,f]
 cases p:R.flip k <;> simp [lineSi,digit,hit,p,amt,e] -- tune
-- door all incident links. AG same 
lemma sent_last (e:Edge (Skye.Seat n)): (sent s e).2=s.s.perm e.2:=by unfold sent; rw [ProjectorNext.Equivariance.send_formula]; split <;> rfl
lemma door_p (V:tangD n) (e:Edge (Skye.Seat n)): door_b s 1 V e = amt s.s e.2 • dyeX s.charge (V (sent s e)):=by
 let T:= V (sent s e); have hv(b:Bool)(x:tangD n)(e:Edge (Skye.Seat n)): cape_v b x e=dyeX b (x e):=by cases b <;>rfl
 let U:= ProjectorNext.Equivariance.pulledDirection s.s ((assembly n).embed s.b) (1:Pane n); rw [show door_b s 1 V e= _ from (show _=dyeX s.charge (U V e) from hv s.charge (U V) e)]; change dyeX s.charge (ProjectorNext.Equivariance.roll s.s ((assembly n).embed s.b) (1:Pane n) e T)= _ 
 rw [ProjectorNext.Equivariance.roll_apply]; cases p:s.s.flip e.2<;> simp [amt,p,T]
lemma sunCap (C:Gem)(A:SU.group.Color)(u:Nonwrapping X.val.2 X.val.1)(h:10 ≤ (More n).val)(t:ℝ): let V:=(moveHub s X); Agrees V.val.2 (door_b s 1 (gateC X.val.1 t (hem C A))) (gateC V.val.1 t (hem (gird s.s C) (dyeX s.charge A))):=by
 intro V e q l; let R:=s.s; let Y:=sent s e; let a:= X.val.1; let b:=V.val.1; let D:= dyeX s.charge;
 rw [door_p]; change amt R e.2 • D (t • formC (hem C A) Y.2 (stem a Y.1))=t • formC _ e.2 (stem b e.1);
 rw [mid_c,mid_c,map_smul D t,map_smul,map_sum, smul_comm (amt R _) t,smul_comm (amt R _) (1/2:ℝ),←Equiv.sum_comp R.perm, smul_sum]; congr 1; congr 1;
 apply sum_congr rfl; intro i _; rw [map_smul,show lineSi (stem a Y.1) Y.2 (R.perm i)= _ from mid_valuation s e ⟨q,l⟩ u h i,show Y.2= _ from (show Y.2=R.perm e.2 from sent_last ..)]
 let z:= D A; let L:=C.val (R.perm i) (R.perm e.2);
 change amt R e.2 • ((amt R i* _) • D (L • A))= _ • ((amt R i*amt R e.2*L) • z); rw [map_smul]; simp only [smul_smul]; congr 1; ring
lemma moonCap (C:Sut)(A:SU.group.Color)(u:Nonwrapping X.val.2 X.val.1)(h:10 ≤ (More n).val)(t:ℝ): let V:=(moveHub s X); Agrees V.val.2 (door_b s 1 (gateT X.val.1 t (loomH C A))) (gateT V.val.1 t (loomH (girdS s.s C) (dyeX s.charge A))):=by
 intro V e q l; let R:=s.s; let Y:=sent s e; let a:= X.val.1; let b:= V.val.1; let D:=dyeX s.charge;
 rw [door_p]; change amt R e.2 • D (t • formT (loomH C A) Y.2 (stem a Y.1))=t • formT _ e.2 (stem b e.1);
 rw [mid_s,mid_s,map_smul D t,map_smul,map_sum,smul_comm (amt R _) t,smul_comm (amt R _) (1/3:ℝ), ←Equiv.sum_comp R.perm,smul_sum]; congr 1; congr 1; apply sum_congr rfl; intro i _
 rw [map_smul,map_sum, ←Equiv.sum_comp R.perm, smul_sum,smul_sum,smul_sum]; apply sum_congr rfl; intro j _;
 have hv(z: Axis): lineSi (stem a Y.1) Y.2 (R.perm z)= amt R z * lineSi (stem b e.1) e.2 z:= mid_valuation s e ⟨q,l⟩ u h z
 rw [hv i,map_smul,hv,show Y.2=R.perm e.2 from sent_last ..]
 let F:= C.val (R.perm j) (R.perm i) (R.perm e.2); let Z:= D A; change amt R e.2 • ((amt R i*_) • ((amt R j*_) • D (F • A))) = lineSi _ _ i • (lineSi _ _ j • ((amt R j*amt R i*amt R e.2*F) • Z)); rw [map_smul]; simp only [smul_smul]; congr 1; ring
end Fren
end Layout
end Lenten
end YM.CF.TableF
end
