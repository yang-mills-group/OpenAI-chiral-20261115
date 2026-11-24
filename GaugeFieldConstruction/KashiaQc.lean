import GaugeFieldConstruction.UshioQc
/-! P and K transforms signed -/
set_option autoImplicit false
set_option synthInstance.maxSize 8400
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S) (s:Signed) (v:UpAngleQc Y)
local notation "H"=> spinFrame five s
lemma CozioS_tail (x:Points (n+1)): riders (CozioQc _ s x)=CozioQc _ s (riders x):= PiLp.ext fun i=> rfl
lemma CozioS_head (x:Points (n+1)): helm (CozioQc _ s x)=BoxmoveQc s (helm x):=rfl
include v in
lemma runPierQc (a:Axis)(b c:l)(h:PierQc (S:=S) a b c): PierQc (S:=S) (s.perm a) (H b) (pay (s.flip a) (H c)):=by
 intro n L k; let X (i:Fin n):= spinFrame five s⁻¹ (L i); have he:(fun i=> H (X i))=L:= funext fun i=> Loft.both ..
 ext1 p; rw [←he,pays, HermSpotQc Y s v]
 let u:= flipTestQc s p; have hx:=h _ X k
 cases q:s.flip a
 · rw [pay_false,HermSpotQc Y s v,hx,pays,tiltPayQc, q]; rfl
 rw [pay_true,map_neg]; change - (S.spot _ _ (H c) p) =_; rw [HermSpotQc Y s v,hx,pays,tiltPayQc, q,pay_true,map_neg,neg_neg]
-- comparing sign payroll
structure SignCostsQc (s:Signed) (K R:Bills)(c:Bool):Prop where
   price n j a x:(R n j).K (s.perm a) (CozioQc _ s x)=pay (s.flip a) (pay c ((K n j).K a x))
lemma SpotPaperQc (i):SignCostsQc s (postage i) (postage (s.perm i)) (s.flip i):=by
 constructor; intro n k a x; change basis _ _=_; change _=pay (s.flip a) (pay (s.flip i) (basis i a)); by_cases p:a=i
 · subst a; simp
 simp [p]
lemma AnglePriceQc (Ω): SignCostsQc s (rpm Ω) (rpm (Stage.conjS s.ortho Ω)) false := by
 constructor; intro n k a x; rw [pay_false]; change (desk _ _).K _ _= pay _ ((desk _ _).K _ _); rw [angle,angle, CozioS_tail, CozyPqc, CozyPqc,←map_sub]
 rw [← zBoxQc s, Stage.conjS]; simp only; rw[M4.move_mul, M4.move_mul, show M4.move (star s.ortho.val) (BoxmoveQc _ _) = _ from ?_] -- tune anti.rot
 · rfl
 exact Ortho.inv_move ..
lemma SpinPrintQc (T:SymT)(i j): spinFrame five s (prints T i j)=pay ((s.flip i).xor (s.flip j)) (prints T (s.perm i) (s.perm j)):=by
 unfold prints pens; rw [← Loft.spin_lift,T.property.2]; simp only [Cauchy.Row.Record.sym_turn, Cauchy.Row.Record.fee_turn] -- tune names
 cases (s.flip i).xor (s.flip j) <;> simp
include v in
lemma spinReachQc (T:SymT)(K R:Bills)(c:Bool)(p:SignCostsQc s K R c)(A B:l)(h:Reaches S (prints T) K A B): Reaches S (prints T) R (H A) (pay c (H B)):=by
 intro n L k t b g; let X (i:Fin n):= spinFrame five s⁻¹ (L i); have hv:(fun i=> H (X i))=L:=funext fun i=>Loft.both ..; let z:=MakerQc s b t k g; let J:=prints T
 let Y₀:=update X k A; let L':= update L k (H A); have ht:(fun i:Fin n=>H (Y₀ i))=L':=funext fun i=>by
    unfold L' Y₀; by_cases e:i=k; · subst i; rw [update_self,update_self]
    rw [update_of_ne e,update_of_ne e]; exact congr_fun hv i -- tune
 have e:S.spot L k (pay c (H B)) t= pay c (S.spot X k B (flipTestQc s t)):=by
    rw [←hv]; cases c
    · exact HermSpotQc Y s v _ X _ t
    rw [pay_true,map_neg]; change - (S.spot _ _ (H B) t)=_; rw [HermSpotQc Y s v]; rfl
 rw [e, h _ _ _ _ _ z]; unfold delta
 let iK (i j:Axis):=testcut (K n k) (flipTestQc s t) (moveBulbQc s b) z.cared i j
 let iR (i j:Axis):=testcut (R n k) t b g.cared (s.perm i) (s.perm j)
 have w(i j:Axis): flipTestQc s (iR i j)=pay ((s.flip i).xor (s.flip j)) (pay c (iK i j)):=by
    ext1 x; rw [flipAtQc]
    let V:= flipTestQc s t; let a:=s.flip i; let d:=s.flip j; have hb(x:Points n):t (CozioQc n s x)=V x:= rfl
    have he (c:Bool)(p:Test (n+1)): pay c p x=pay c (p x):=by cases c <;> rfl
    unfold iR iK; rw [testcut_v,he,he,testcut_v, tiltmuQc, p.price,CozioS_head,CozioS_tail,flipAtQc]; cases u:s.flip i <;> cases q:s.flip j<;> cases c <;> simp[pay] -- tune XOR
 let E(i j:Axis):= S.armed J Y₀ i j (iK i j); let F(i j:Axis):= S.armed J L' (s.perm i) (s.perm j) (iR i j)
 have he(i j:Axis): F i j=pay c (E i j):=by
    let b:Bool:=(s.flip i).xor (s.flip j); have he:J (s.perm i) (s.perm j)=pay b (H (J i j)):=by rw [show H (J i j)=pay b _ from SpinPrintQc .., pay_pay]
    have hp:S.tagged L' (H (J i j)) (iR i j)=S.tagged Y₀ (J i j) (pay b (pay c (iK i j))):=by
       rw [←w,tagged_cost,tagged_cost,← HermesQc Y s v, show Fathom.add (H (J i j)) L'= (fun x=>H ((Fathom.add (J i j) Y₀) x)) from funext fun zΘ=> by rw[←ht]; refine Fin.cases ?_ ?_ zΘ <;> simp [Fathom.add]]
    unfold F E armed; rw [he]
    have u (c:Bool)(L:Fin n → UV five)(x:l)(t:Test (n+1)):S.tagged L (pay c x) t= pay c (S.tagged L x t):=by cases c; rfl; rw[pay_true,map_neg]; rfl
    have w (c:Bool)(L:Bond (n+1))(t:Test (n+1)): L (pay c t)=pay c (L t):=by cases c; rfl; exact map_neg ..
    rw[u,hp,w,w,pay_pay] -- tune

 let ψ(i j:Axis):= S.armed J L' i j (testcut (R n k) t b g.cared i j)
 rw[show (∑ i:Axis,∑ j:Axis,S.armed (prints T) (update L k _) i j (testcut (R n k) _ b _ i j))=∑ i:Axis,∑ j:Axis,F i j from ?_]
 · change pay c (∑ i:Axis,∑ j:Axis,E i j)= _; simp_rw [he]; cases c <;> simp[Finset.sum_neg_distrib]
 change (∑ i:Axis,∑ j:Axis,ψ i j)=∑ i:Axis,∑ j:Axis,ψ (s.perm i) (s.perm j); have HW (f:Axis→ℂ): (∑ i:Axis,f i)= (∑ i:Axis,f (s.perm i)):= (Equiv.sum_comp _ f).symm
 nth_rw 1 [HW]; exact Finset.sum_congr rfl fun i _=> HW _ -- tune parser f:
#print axioms spinReachQc
end YM.GaugeFieldConstruction.Ember.Hulse
