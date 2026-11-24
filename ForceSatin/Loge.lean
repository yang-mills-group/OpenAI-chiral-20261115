import ForceSatin.ChoraleSpin
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip BPress.Spin.Blank Flare
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu Lifted Loaves Verses
open Lamour
open Next.Free
open _root_.YM.Regis.Circuit.SpringDay Spring
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra

noncomputable def WickP (x y:Bite):= zTariff [x,y]
noncomputable def originCL : Slot:=Classical.arbitrary _
noncomputable abbrev tradeW (i j:SpinIdx)(x:Cover):= WickP ⟨0,j,originCL,false⟩ ⟨x,i,originCL,true⟩
def Flash (i j:SpinIdx)(x:Stationary.Gaia):ℂ:=∑ a:Axis,rubrix i j a*fettle a x
structure CompassChar (V:ℕ→Side)(M:ℕ→Jill.Male) :Prop where
 even : ∀ i,Even (V i).val
 VC : Tendsto (fun i=>(V i).val) atTop atTop
 MC : Tendsto (fun i=>(M i).val.val) atTop atTop
 born :∀ i,IsStarProjection (FlatPaneP 4 (M i) (V i))
variable {V M}(h:CompassChar V M)
namespace CompassChar
variable {i j:SpinIdx}
include h
lemma stance (L:List Bite): Tendsto (fun i=> runes (bells (M i) (h.born i)) L) atTop (𝓝 (zTariff L)):=by
 choose v P using fun i=> phoz (h.born i); simp_rw [← flick _ _ _ (P _)]; refine Metric.tendsto_nhds.mpr fun ε p=> ?_; obtain ⟨n,e⟩:= trueMean L (ε/2) (half_pos p); filter_upwards [h.VC.eventually_ge_atTop n,h.MC.eventually_ge_atTop n] with i y u; rw [dist_eq_norm]; exact (e _ _ y u (h.even i) (h.born i) _ (P i)).trans_lt (half_lt_self p)
lemma stalk (x y:Bite): Tendsto (fun i=> bells (M i) (h.born i) x y) atTop (𝓝 (WickP x y)):=by
 simpa only [twoPair,WickP] using stance h [x,y]
-- full functionals WA. limit existence & literal mean orientation.
lemma opus (L:List Bite): zTariff L=runes WickP L:=tendsto_nhds_unique (h.stance L) (offer_v _ _ (stalk h) L)
lemma Cobb (x:Cover)(e:i∉plusHalf)(f:j∈plusHalf): Tendsto (fun k=> CupM (M k) (V k) i j x) atTop (𝓝 (tradeW i j x)):=by
 let u:=stalk h (⟨0,j,originCL,false⟩:Bite) ⟨x,i,originCL,true⟩; apply Tendsto.congr _ u; intro b; exact (pastoral _ _ _ _ rfl rfl e f).trans (by dsimp; rw [sub_zero, if_pos rfl]) -- tune
lemma stars (x y:Bite)(m:y.hand=false)(n:x.hand=true)(e:x.spin∉plusHalf)(q:y.spin∈plusHalf): let v:= if x.cost=y.cost then tradeW x.spin y.spin (x.root-y.root) else 0; WickP y x=v ∧ WickP x y= -v:=by
 intro v; have he: WickP y x=v:=by
    apply tendsto_nhds_unique (h.stalk y x); simp_rw [pastoral _ _ x y m n e q]; unfold v; split_ifs; exact Cobb h _ e q; exact tendsto_const_nhds
 rw [←he]; refine ⟨rfl,tendsto_nhds_unique (h.stalk x y) ?_⟩; simp_rw [bells_flip (M:=M _) _ m n (fun l=>e (l▸q))]; exact (h.stalk y x).neg
lemma dark (x y:Bite)(p:x.hand=y.hand):WickP x y=0:= tendsto_nhds_unique (stalk h x y) (tendsto_const_nhds.congr fun i=> by unfold bells Loaves.tooth paceSing; simp [p])
end CompassChar
open _root_.YM.Regis.Circuit.SpringDay.Lyra
lemma sumsJet {ι: Type*}(S: Finset ι)(L:List Cover)(F:ι→ Cover→ℂ)(x:Cover):muJet L (fun x=>∑ i∈S,F i x) x= ∑ i∈ S, muJet L (F i) x:=by induction L generalizing x with| nil=>rfl| cons i l ih=> simp_rw [muJet_cons, ih, ← Finset.sum_sub_distrib]

abbrev LiltKey:= {k: Side // Even k.val} × Jill.Male
abbrev lumen : Lyra LiltKey:=⟨fun i=>i.1.val,fun i=> micaO i.1.val,fun i=>i.1.property⟩

lemma swing (a:Axis)(i:Side)(p:Jill.Male)(x:Cover):skyPrice (micaO i) (fun j=> imp a p (tmap (glen (micaO i) j))) x= skyPrice (micaO i) (fun j=> terra₀ p a (mel j)) x:=by simp only [micaO,glen,add_zero]; rfl
lemma Moonlight (i j:SpinIdx)(L:List Cover):∃ C:ℝ,0<C∧∀ V:ℕ→Side, ∀ M:ℕ→ Jill.Male, (∀ i, Even (V i).val) → Tendsto (fun i=>(V i).val) atTop atTop → ∀ x:Cover,x≠0 → ∀ᶠ k:ℕ in atTop, ‖muJet L (CupM (M k) (V k) i j) x-muJet L (Flash i j ∘ scape) x‖ ≤ C/rally x^(4+L.length):=by
 let f(k:LiltKey):=k.2; let S(a:Axis):= magnum lumen f a
 choose C e T using fun a:Axis=> timely (S a) (matterTrade a) L
 let r(a:Axis):= rubrix i j a; let W:=∑ a:Axis, ‖r a‖*C a; have hV:0≤ W:= Finset.sum_nonneg fun i _=> mul_nonneg (norm_nonneg _) (e i).le; refine ⟨W+1,by positivity,fun V M h P x b=>?_⟩; let F(k:ℕ):LiltKey:=(⟨V k,h k⟩,M k)
 let t:=rally x^(4+L.length); have ht:0<t:=pow_pos (planePeak b) _; filter_upwards [(eventually_all.mpr fun a:Axis=> T a F (fun i=> juneB (V i) (h i)) P x b)] with k H
 let X(a:Axis):= r a • (warble (S a) (F k)); let Y(a:Axis):= r a • (fettle a ∘ scape); let U:= Finset.univ (α:=Axis); let d:=V k
 rw [show CupM (M k) d i j=(fun x=> ∑ i∈U,X i x) from funext (fun x=> Finset.sum_congr rfl fun l (_:l∈U)=> congrArg (r l*·) (swing l d (M k) x).symm), show Flash i j ∘ scape= (fun x=> ∑ i∈U,Y i x) from rfl, sumsJet,sumsJet,← Finset.sum_sub_distrib]
 exact (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun i=> ‖r i‖*C i/t) (fun l _=> by
    have ho:=H l; unfold X Y; rw [muJet_mul,muJet_mul,Pi.smul_apply, Pi.smul_apply,←smul_sub,norm_smul,_root_.mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact (show _≤_ by simpa only [Nat.add_zero, (_root_.Function.comp_apply)] using ho))).trans (by rw [← Finset.sum_div]; gcongr; linarith))
include h
lemma SunRay (i j:SpinIdx)(L:List Cover)(p:i∉plusHalf)(u:j∈plusHalf):∃ C:ℝ,0<C∧∀ x:Cover,x≠0→ ‖muJet L (tradeW i j) x-muJet L (Flash i j ∘ scape) x‖ ≤ C/rally x^(4+L.length):=by
 obtain ⟨C,c,X⟩:=Moonlight i j L; exact ⟨C,c,fun x e=> le_of_tendsto (((muJet_go L (fun x=> h.Cobb x p u) x).sub_const _).norm) (X V M h.even h.VC x e)⟩
#print axioms CompassChar.opus
#print axioms CompassChar.stars
#print axioms SunRay
end YM.CF.Papyrus.Franc.SatinForce
