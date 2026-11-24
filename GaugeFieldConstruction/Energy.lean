import GaugeFieldConstruction.Pryor
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
open TableF.Axon Siete Lenten.ModuleB MultiNext.SignedSource Lyre Banjo Analysis
variable {c f:Side}{M:Male}{Z:Scree.Hub f}{P:BudgetPoint}{Y:InkD f}{d b a C s h:ℝ}{r k:ℕ}{g: Finset (Dwell f)→ℝ}
variable (p:PressB P Z Y h C)(u:Nonwrapping Z.val.2 Z.val.1)(v:∀ i,0≤g i)(dV:∀ U,BedP P U Y Z g)
variable (q:10 ≤(More f).val)(t:0 ≤ b)(l:b ≤1)(κ:1≤ s)(wZ:Stakes s b Z P) (vM:r=3→landA M Z.val.1 Y P h=0)(gR:r ≤3)
include p u v dV wZ vM gR q t l κ
abbrev DepotPrice (s:ℝ):= 1 + (4*s+4)+(16*s^2+1)
variable (Qt: quote_B M (orbitPH (Y 1)) Z.val.1 h r)
include Qt
lemma mast_taylor {x:tangD f} (Q:StrongE P Z s b x)(k:ℕ)(F:Fin k→ tangD f)(e:∀ i,StrongE P Z s b (F i)): Archive M r Z.val.1 h b (DepotPrice s) (Zinc g) (Axis_Price Y x F 1):=by -- fix binder x
 have hs:0 ≤ s:= zero_le_one.trans κ; have ht:0 ≤DepotPrice s:=by unfold DepotPrice; positivity
 have hA:=Zinc_pos v; let H1(x:tangD f)(K:StrongE P Z s b x):= swept1 p u v dV q t l κ wZ vM gR x K
 let H2(x y:tangD f)(Hx:StrongE P Z s b x)(Hy:StrongE P Z s b y):=swept₂ (M:=M) p u v dV q t l κ wZ gR x y Hx Hy
 match k with
 | 0=>
    let X:=mastX Y 0 F; let W:=mastX Y 0 ![x]; let V:=mastX Y 0 ![x,x];
    have hv:Rode Z.val.1 1 (Zinc g) X:=by simpa only [Finset.univ_eq_empty,prod_empty] using (mast_hunt p u v dV F (q:=fun i=>Fin.elim0 i) (t:=fun _=>0) (Nat.zero_le _)) -- tune
    have hz:= (H2 x x Q Q).scalar (1/2)
    have hp:‖(1/2:ℝ)‖≤1:=by rw [Real.norm_of_nonneg (by positivity)]; norm_num
    have hx:= hz.weaken (mul_le_of_le_one_left (by positivity) hp) t hA
    have he: Axis_Price Y x F 1=X+W+(1/2:ℝ) • V:=by change X+(1:ℝ) • mastX Y 0 (Fin.cons x F)+((1:ℝ)^2/2) • mastX Y 0 (Fin.cons x (Fin.cons x F))=_; simp only [one_pow,one_smul]; unfold W V; rw [show Fin.cons x F= ![x] from (funext fun i=>by fin_cases i; rfl)]; rfl
    rw [he]; exact ((Archive.pay₁ hv (by unfold X; rw [mast_flat]; exact Qt) t zero_le_one hA).fuse (H1 x Q)).fuse hx
 | 1=>
    have he: Axis_Price Y x F 1=mastX Y 0 ![F 0]+mastX Y 0 ![x,F 0]:=by change mastX Y 0 F+(1:ℝ) • mastX Y 0 (Fin.cons x F)=_; rw [one_smul]; congr <;> ext1 i <;> fin_cases i <;> rfl
    rw [he]; exact ((H1 _ (e 0)).fuse (H2 _ _ Q (e 0))).weaken (by unfold DepotPrice; linarith) t hA
 | 2=>
    have he: Axis_Price Y x F 1= mastX Y 0 ![F 0,F 1]:=by change mastX Y 0 F= _; rw [show mastX Y 0 F = _ from (congrArg (mastX Y (m:=2) 0) (show F= ![F 0,F 1] from funext fun i=> by fin_cases i <;> rfl))] -- tune k
    rw [he]; exact (H2 _ _ (e 0) (e 1)).weaken (by unfold DepotPrice; linarith) t hA
 | k+3=> exact Archive.null t ht hA
omit p u v dV wZ vM gR q t l κ Qt
variable {X:SM f→ℝ}{o:Skye.Seat f}
lemma arch_sent{Q:Op (Single f)}(h:Archive M r Z.val.1 d b C X Q): SentK Z.val.1 Q:=by
 obtain ⟨U,V,R,p,h,v,k,h',e⟩:= h.bill; rw [p]; exact ((h.addH v).addH k).sent
lemma sent_sub{Q U:Op (Single f)} (a:SentK o Q)(u:SentK o U):SentK o (Q-U):= by
 intro i j t; by_cases e:Q i j=0; · exact u i j fun v=> t (by rw [Matrix.sub_apply,e,v,sub_zero])
 exact a i j e
lemma Archive.sheet{ι:Type*}(e:∀ i,0≤X i)(L:ι → Op (Single f))(T:Finset ι)(p:∀ i∈T,Archive M r o h b C X (L i))(v:0≤b):Archive M r o h b ((T.card:ℝ)*C) X (∑ i∈T,L i):=by
 induction T using Finset.induction_on with
 | empty=>rw [card_empty,Nat.cast_zero,zero_mul,sum_empty]; exact Archive.null v le_rfl e
 | @insert i S u H=> rw [card_insert_of_notMem u,Nat.cast_add,Nat.cast_one,add_mul,one_mul,sum_insert u, add_comm (S.card*_ : ℝ)]; exact (p i (mem_insert_self ..)).fuse (H (fun i j=> p i (mem_insert_of_mem j))) -- tune
abbrev DepTotal (s:ℝ):= DepotPrice s + xHoch 6 * (4*s)^6
include p u v dV wZ vM gR q t l κ Qt
lemma mast_d (x:tangD f)(hc:Chamber Z P x)(s':StrongE P Z s b x)(F:Fin k → tangD f)(e:∀ i,StrongE P Z s b (F i))(ε:k ≤6) : Archive M r Z.val.1 h b (DepTotal s) (Zinc g) (mastX Y x F):=by
 let Q:=Axis_Price Y x F 1; have hp:Archive M r Z.val.1 h b (DepotPrice s) _ Q:= mast_taylor p u v dV q t l κ wZ vM gR Qt s' k F e
 have ht:0≤ xHoch 6:=zero_le_one.trans (multip 6).choose_spec.1 -- tune
 have he:0 ≤ s:=zero_le_one.trans κ
 have hh:Rode Z.val.1 (xHoch 6*(4*s)^6*b^3) (Zinc g) (mastX Y x F-Q):=by
    refine ⟨sent_sub (mast_support p u F) (arch_sent (Z:=Z) hp),fun i=>?_⟩
    have hz:= Axis_Pay p dV 1 t l κ i.1 i.2 (by simp) F ε (fun i=>StrongE.tap (e i)) (StrongE.tap s') hc; rw [one_smul] at hz; exact hz.trans (mul_le_mul_of_nonneg_left (Zinc_big v i) (by positivity))
 exact Eq.mpr (congrArg (fun x=>Archive M r Z.val.1 h b (DepTotal s) (Zinc g) x) (add_sub_cancel Q (mastX Y x F)).symm) (hp.fuse (Archive.pay₃ (hh.liftH (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t l gR) (by positivity)) (Zinc_pos v)) t (by positivity) (Zinc_pos v))) -- tune add_sub_cancel
-- cost on all jets BEFORE screen. every unit direction.
lemma MastBill {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](H:Set E)(W:E→ tangD f)(A:LocalCurve P Z W H s b)(V:∀ k ≤6,∀ u:Fin k→ E,(∀ i, u i∈H)→ StrongE P Z s b (iteratedFDeriv ℝ k W 0 u))(x:Fin k→E)(y:∀ i,x i∈H)(l':k≤6): Archive M r Z.val.1 h b (DevelopCost* DepTotal s) (Zinc g) (Matrix.of fun (i j:Single f)=> iteratedFDeriv ℝ k (portE Y i j∘ W) 0 x):=by
 let R(j:OrderedFinpartition k):=fieldBlock W x j
 have hs:StrongE P Z s b (W 0):= by simpa using V 0 (by omega) Fin.elim0 (fun i=>Fin.elim0 i)
 let Q(j:OrderedFinpartition k):=mastX Y (W 0) (R j)
 have ht(j): Archive M r Z.val.1 h b (DepTotal s) (Zinc g) (Q j):= mast_d p u v dV q t l κ wZ vM gR Qt _ A.home hs _ (fun i=> V _ ((j.partSize_le i).trans l') _ (fun k=> y _)) (j.length_le.trans l')
 have hu:pingS P.threshold Z.val.2 (increment 1 (W 0)):=by simpa using A.home.2 1 (by simp)
 rw [show Matrix.of (fun i j: Single f=> _)=∑ i:OrderedFinpartition k,Q i from ?_]; swap
 · ext i j; rw [Matrix.of_apply,iteratedFDeriv_comp (PortProof p dV _ hu i j) A.smooth (Nat.cast_le.mpr l'),FormalMultilinearSeries.taylorComp,_root_.sum_apply,Matrix.sum_apply]; rfl
 apply (Archive.sheet (Zinc_pos v) Q univ (fun i _=> ht i) t).weaken _ t (Zinc_pos v); rw [card_univ]; refine mul_le_mul_of_nonneg_right (single_le_sum (f:=fun i=> (↑(Fintype.card (OrderedFinpartition i)):ℝ)) (fun _ _=>by positivity) (mem_range.mpr (show k<7 from by omega))) ?_; unfold DepTotal DepotPrice; have hp:=zero_le_one.trans κ; have hx:0 ≤xHoch 6:= zero_le_one.trans (multip 6).choose_spec.1; positivity
end Boom
end YM.CF.TableF
end
