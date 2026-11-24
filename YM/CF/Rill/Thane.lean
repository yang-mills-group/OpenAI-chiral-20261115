import YM.CF.Rill.Osc
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Jet
section cost
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n j:ℕ}{P X Z:SU.group.El}{F H:E→ SU.group.El}{V:E}{d e:ℝ}
abbrev Tender(F:E→ SU.group.El)(z:E)(a:ℝ)(n:ℕ):Prop:= Shake (SU.group.mat∘ F) z a n
structure Wind(d:ℝ)(p:SU.group.El→ SU.group.El→ SU.group.El)(n:ℕ)(C:ℝ):Prop where
 pos:0≤C
 duty : ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{F H:E→ SU.group.El}{V:E},{e:ℝ}→e≤d→ Tender F V e n→Tender H V e n→Tender (fun i=>p (F i) (H i)) V (C*e) n
-- chart site. assume Sc smooth all sites along pair curves. Show uniform receipt by finite dimensional Prop compact. proof via evaluating third/fourth variables extension(Shift) local
variable (p: SU.group.El→ SU.group.El→ SU.group.El)(n:ℕ)
abbrev Clout:= SU.group.El× SU.group.El
abbrev Chalk:= SU.group.Color× SU.group.Color
def slat(x:Clout)(z:Chalk): Clout:= (SU.group.lieExp z.1*x.1, SU.group.lieExp z.2*x.2)
def kflip (x:Clout)(z:Clout):Chalk:=(LocalH.snap G (z.1*x.1⁻¹), LocalH.snap G (z.2*x.2⁻¹))
lemma fleck (x:Clout):kflip x x=0 ∧ ContinuousAt (kflip x) x∧∀ᶠ i in 𝓝 x, slat x (kflip x i)=i:=by
 have h(y:SU.group.El):
    let V(v:SU.group.El):= v*y⁻¹; let F:=LocalH.snap G ∘V
    F y=0∧ContinuousAt F y ∧∀ᶠ i in 𝓝 y, SU.group.lieExp (F i)*y=i:=by
    intro V F; have he:V y=1:=mul_inv_cancel _; have hp: Continuous V:=by unfold V; fun_prop
    refine ⟨?_, (show ContinuousAt SU.group.plog (SU.group.mat (V y)) from by rw [he,Gauge.mat_one]; exact SU.group.plog_diff.continuousAt).comp (f:=SU.group.mat∘ V) (SU.group.continuous_mat.comp hp).continuousAt,?_⟩
    · simp only [F,Function.comp_apply,he, LocalH.snap]; exact (show _ from by simpa using SU.group.plog_left.self_of_nhds)
    have hx:= (show Tendsto V (𝓝 y) (𝓝 1) from he ▸ hp.continuousAt).eventually SU.group.plog_right; filter_upwards [hx] with i t; change SU.group.lieExp (SU.group.plog (SU.group.mat (V i)))*_= _; rw [t]; unfold V; simp [mul_assoc]
 obtain ⟨hP,p,P⟩:=h x.1; obtain ⟨hV,v,V⟩:=h x.2; refine ⟨Prod.ext hP hV,(p.comp continuousAt_fst).prodMk (v.comp continuousAt_snd),?_⟩
 filter_upwards [continuousAt_fst (p:=x)|>.eventually P,continuousAt_snd (p:=x)|>.eventually V] with y k j; exact Prod.ext k j
def cling (p: SU.group.El→ SU.group.El→ SU.group.El)(x:Clout)(z:Chalk):= SU.group.mat (Function.uncurry p (slat x z))
abbrev Coerce(p: SU.group.El→ SU.group.El→ SU.group.El)(n:ℕ):=∀ (x:Clout), ContDiffAt ℝ (↑n) (fun i:Chalk× Chalk=>cling p (slat x i.1) i.2) (0,0)
lemma hole (h: Coerce p n): ∃ K:ℝ,0≤K∧∀ x, Shake (cling p x) 0 K n:=by
 have hp(x:Clout):slat x 0=x:=by simp [slat]
 have hh(j:Fin (n+1)):Continuous (fun x=>‖iteratedFDeriv ℝ (j:ℕ) (cling p x) 0‖):=by
    apply continuous_iff_continuousAt.mpr; intro x; obtain ⟨t,v,h'⟩:=fleck x; let V(y:Chalk× Chalk):=iteratedFDeriv ℝ (j:ℕ) (cling p (slat x y.1)) y.2; let z(u:Clout):= (kflip x u,(0:Chalk)); have hs: ContinuousAt V (z x):=by unfold z; rw [t]; exact (Warm.together (h x)).light j (Nat.le_of_lt_succ j.isLt); -- tune
    refine ((hs.comp (f:=z) (v.prodMk continuousAt_const)).norm).congr_of_eventuallyEq (h'.mono ?_); intro y he; change _=‖iteratedFDeriv ℝ (j:ℕ) (cling p (slat x _)) 0‖; rw [he]
 choose m q using fun j=> (isCompact_univ (X:=Clout)).bddAbove_image (hh j).continuousOn
 let C:=∑ i, |m i|; refine ⟨C,by unfold C; positivity,fun x=>⟨by unfold C; positivity,?_,fun k v t=>?_⟩⟩
 · have he :=(Warm.together (h x)).today; change ContDiffAt ℝ (↑n) (cling p (slat x 0)) 0 at he; rwa [hp] at he
 let z:Fin (n+1):=⟨k,Nat.lt_succ_of_le t⟩; exact (q z (Set.mem_image_of_mem _ (Set.mem_univ x))).trans ((le_abs_self _).trans (single_le_sum (f:=fun i=>|m i|) (fun i _=>abs_nonneg _) (mem_univ z)))
lemma ank(n:ℕ) :∃ d C:ℝ, 0<d∧1≤C ∧ ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](F:E→ SU.E){e:ℝ}{V:E} ,e≤d →Tender F V e n→Shake (fun i=> LocalH.snap G (F i*(F V)⁻¹)) V (C*e) n:=by
 obtain ⟨H,h,H'⟩:= Jet.payment_for n (S:={1}) isCompact_singleton SU.group.plog (fun x hx=>(Set.mem_singleton_iff.mp hx).symm ▸ SU.group.plog_diff.of_le le_top)
 let J:=(fun x:SU.E=>SU.group.mat x); have hv:Continuous J:=SU.group.continuous_mat
 obtain ⟨T,hT,T'⟩:= Jet.payment_for n (S:=(J '' Set.univ)×ˢ(J '' Set.univ)) ((isCompact_univ.image hv).prod (isCompact_univ.image hv)) (fun x:SU.group.Mat× SU.group.Mat=>x.1*x.2) (fun _ _=>contDiffAt_fst.mul contDiffAt_snd)
 let b:= max (Shake.quota n*T) 1; let C:= max 1 (Shake.quota n*H*b)
 have hp:0<b:=lt_of_lt_of_le zero_lt_one (le_max_right ..)
 refine ⟨min 1 (1/b),C,lt_min zero_lt_one (by positivity), le_max_left ..,@fun E _ _ F e V g k=>?_⟩
 let X(i:E):= F i*(F V)⁻¹; let Z(i:E):=(SU.group.mat (F i), SU.group.mat ((F V)⁻¹))
 have hx:SU.group.mat ∘ X= fun i=>(Z i).1*(Z i).2 := funext fun i=>Gauge.mat_mul ..; have hA:SU.group.mat (X V)=1:=by simp [X]
 have hb :Shake (SU.group.mat∘X) V (b*e) n:=by
    rw [hx]
    exact ((k.team (Shake.holds (SU.group.mat ((F V)⁻¹))|>.bag k.price)).thorn (Shake.pick (T' _ ⟨Set.mem_image_of_mem J (Set.mem_univ (F V)), Set.mem_image_of_mem _ (Set.mem_univ ((F V)⁻¹))⟩)) (g.trans (min_le_left ..))).bag (by unfold b; rw [←mul_assoc]; gcongr; exact k.price; exact le_max_left ..)
 exact (hb.thorn (Shake.pick (H' _ (Set.mem_singleton_iff.mpr hA))) ((mul_comm b e).le.trans ((le_div_iff₀ hp).mp (g.trans (min_le_right ..))))).bag (by unfold C; rw [←mul_assoc,←mul_assoc]; gcongr; exact k.price; exact le_max_right ..)
lemma buy (h:Coerce p n):∃ a:ℝ,0<a∧ ∃ C:ℝ,1≤C ∧ Wind a p n C:=by
 obtain ⟨b,v,hb⟩:= hole p n h; obtain ⟨d,C,hd,hC,H⟩:= ank n; have hx:= zero_lt_one.trans_le hC
 let B:=max 1 (Shake.quota n*b*C); refine ⟨min d (1/C),lt_min hd (by positivity),B, le_max_left ..,⟨zero_le_one.trans (le_max_left ..),@fun E _ _ F I V e Qv y z=> ?_⟩⟩
 let X(i:E):= (F i,I i); let Q:=X V; let J(i:E):= kflip Q (X i); have hp:=Qv.trans (min_le_left ..); have he:J V=0:=(fleck Q).1; have hs:Shake J V (C*e) n:=(H F hp y).team (H I hp z)
 have hv:ContinuousAt X V:= ((SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isInducing.continuousAt_iff.mpr y.smooth.continuousAt).prodMk ((SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isInducing.continuousAt_iff.mpr z.smooth.continuousAt)
 refine (((hs.thorn (show Shake _ (J V) _ n from he.symm ▸ hb Q) ((mul_comm C e).le.trans ((le_div_iff₀ hx).mp (Qv.trans (min_le_right ..))))).bag ?_).same ?_)
 · unfold B; rw [←mul_assoc,←mul_assoc]; gcongr; exact y.price; exact le_max_right ..
 filter_upwards [hv.eventually (fleck Q).2.2] with i t; exact congrArg (SU.group.mat ∘ Function.uncurry p) t -- tune
end cost
-- furnish Lie
variable (n:ℕ){a:ℝ}
lemma duoK(p:SU.group.El→ SU.group.El→ SU.group.El)(h: ∀ (U V:Chalk× Chalk→ SU.group.El),Scope (l:=n) U (0,0)→ Scope (l:=n) V (0,0)→ Scope (l:=n) (fun i=>p (U i) (V i)) (0,0)):Coerce p n:=by
 intro X; let U(i:Chalk× Chalk):=slat (slat X i.1) i.2; apply h (fun i=>(U i).1) (fun i=>(U i).2)
 · unfold Scope U slat; dsimp only [Function.comp_apply]; simp_rw [Function.comp_def,Gauge.mat_mul]; exact ((SU.group.exp_jet.of_le (m:=↑n) le_top).contDiffAt.comp (f:=fun x:Chalk×Chalk=>x.2.1) (0,0) (by fun_prop)).mul (((SU.group.exp_jet.of_le (m:=↑n) le_top).contDiffAt.comp (f:=fun x:Chalk×Chalk=>x.1.1) (0,0) (by fun_prop)).mul contDiffAt_const) -- tune
 unfold Scope U slat; dsimp only [Function.comp_apply]; simp_rw [Function.comp_def,Gauge.mat_mul]; exact ((SU.group.exp_jet.of_le (m:=↑n) le_top).contDiffAt.comp (f:=fun x:Chalk×Chalk=>x.2.2) (0,0) (by fun_prop)).mul (((SU.group.exp_jet.of_le (m:=↑n) le_top).contDiffAt.comp (f:=fun x:Chalk×Chalk=>x.1.2) (0,0) (by fun_prop)).mul contDiffAt_const)
lemma sailors(q:Chi)(hx:0<a)(p:2*a< firstRadius G):∃ d K:ℝ,0<d∧1≤K ∧ Wind d (fun i j=>i*j) n K ∧ Wind d (fun i _=>i⁻¹) n K∧ Wind d (knit q a) n K:=by
 obtain ⟨d,hd,C,hC,h⟩:= buy _ n (duoK n (·*·) (fun F M g h=>by unfold Scope; simp_rw [Function.comp_def,Gauge.mat_mul]; exact g.mul h)); obtain ⟨b,hb,Z,hZ,hZ'⟩:= buy _ n (duoK n (fun i _=>i⁻¹) (fun F M g h=>by unfold Scope; simp_rw [Function.comp_def,Gauge.mat_inv]; exact ((starL ℝ).contDiff.contDiffAt.comp _ g))); obtain ⟨c,hc,K,hK,H⟩:= buy _ n (duoK n (knit q a) (fun _ _ t v=> knitD q hx p t v))
 let Q:= min d (min b c); let W:=max C (max Z K)
 have hv:1≤W:=hC.trans (le_max_left ..)
 have hx{u x:ℝ}{p}(h:Wind u p n x)(v: Q≤ u)(w:x≤W): Wind Q p n W:=⟨h.pos.trans w,@fun E _ _ F I V a p g t=> (h.duty (p.trans v) g t).bag (mul_le_mul_of_nonneg_right w g.price)⟩
 exact ⟨Q,W,lt_min hd (lt_min hb hc),hv,hx h (min_le_left ..) (le_max_left ..),hx hZ' ((min_le_right ..).trans (min_le_left ..)) ((le_max_left ..).trans (le_max_right ..)),hx H ((min_le_right ..).trans (min_le_right ..)) ((le_max_right ..).trans (le_max_right ..))⟩
end YM.CF.Rill
