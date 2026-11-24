import YM.CF.Swell.Ink
import YM.CF.Hove.Bird
import YM.CF.Leaf.Wren
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open SU Prism Tap Levier Thera Moto Oath Font
variable {N B m:Side} {a b c d e:ℝ}
-- Raw.Ph.Volume fourteen actual open stencil.
variable (P:Op (Single N))(x y o:Site N)(U:Pal)
abbrev arm(P:Op (Single N))(x y:Prism.Rock N)(X:Chin N) : Op SU.Slot:= boxM P x y*(Tulip.track X (Cube.node x.1) (shiftH (Cube.node x.1) (Cube.node y.1))).1
abbrev Φp(p q:Prism.Rock N)(Q:Op (Single N)):SOp N:=fun V=> Tulip.panel p q (arm Q p q V)
abbrev ρlens(P: Op (Single N)): SOp N:= fun V => ∑ p:Prism.Rock N,∑ q:Prism.Rock N, Φp p q P V
lemma χtone (p q:Rock N)(X:SOp N) (V:Pane N) : arm P p q (Tulip.profile V) = Haro.taxi V p q (boxM P p q):=by unfold arm Haro.taxi; rw [Tulip.track_pr]; rfl
lemma stride_X(p q:Prism.Rock N)(V:Chin N)(X:SOp N)(i j:SU.Slot):ρlens P V (p,i) (q,j)=arm P p q V i j:=by
 unfold ρlens Φp; simp_rw [Matrix.sum_apply,panel,Matrix.of_apply,ite_and]; simp -- tune
lemma vision (V:Pane (mid m B))(X:Op (Single (mid m B))) : Hest.boat (ρlens X (Tulip.profile V))= Moto.pay_Y X V:=by
 let Z:=ρlens X (profile V); have h(p q:Prism.Rock (mid m B))(i j:SU.Slot): Z (p,i) (q,j) = Haro.taxi V p q (boxM X p q) i j:=by rw [show Z _ _=arm X p q (profile V) i j from stride_X X p q (profile V) (fun _=>0) i j, χtone X p q (fun _=>0)]
 apply Subtype.ext; change faceD true false Z = _; unfold faceD twinD; rw [Fintype.sum_prod_type]; refine sum_congr rfl ?_; intro i _; change ∑ u:SU.Slot, ∑ j:Single (mid m B),Z (i,u) j • _ = _; simp_rw [Fintype.sum_prod_type (α₂:=SU.Slot)]; rw [sum_comm]; refine sum_congr rfl fun j _=>?_ ; simp_rw [h] -- tune outer.rhs
-- chir support.Crep
abbrev Branded (o:Site N)(P: Op (Single N)): Prop := ∀ i j:Single N,P i j≠0→ i∈Emu.halfS N ∧ j∉Emu.halfS N ∧ (i.1.1=o∨j.1.1=o)
lemma brand_P (x:Site N)(P Q:Op (Single N))(h:Branded x P)(p:Branded x Q):Branded x (P+Q)∧Branded x (P-Q):=by
 constructor <;> intro i j v <;> (by_cases e:P i j≠0; exact h i j e; apply p i j; intro u; apply v; simp [u,not_ne_iff.mp e])
lemma brand_S {ι:Type*}(S:Finset ι)(F:ι→Op (Single N))(p:∀ i∈S,Branded o (F i)):Branded o (∑ i∈S,F i):=by induction S using Finset.induction_on with|empty=> rw [sum_empty]; exact fun _ _ v=>False.elim (v rfl)|insert i S v ih=>rw [sum_insert v]; exact (brand_P _ _ _ (p _ (mem_insert_self ..)) (ih (fun y z=>p y (mem_insert_of_mem z)))).1
lemma slot_φ(R:Pal)(p:culm R=R)(i j:Kt)(v:R i j≠0): i.1∈Lat.plusHalf ∧ j.1∉Lat.plusHalf:=by
 let Y:= plusHalf; let X:=univ.filter (fun i:Kt=> i.1∈ Y); have he: baseF false=Fock.cutM X:=by
    rw [←Hove.binA, show Hove.binV false=cutM Lat.plusHalf from (by unfold binV Fir.angle; rw [if_neg (by decide),sub_sub_cancel]; exact Fir.Adef.trans raising.symm)]; ext p q
    by_cases u:p.1=q.1<;>by_cases w:p.2=q.2<;>simp [cutM,Matrix.kronecker_apply,u,w,X, Matrix.one_apply, Prod.ext_iff,Y]; rw [Prod.ext u w]; simp
 have hu: baseF true=1-cutM X:=by rw [←he]; rfl
 have hx:= Matrix.ext_iff.mpr p i j; unfold culm at hx; rw [he,hu,mul_sub,mul_one, cutM, Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.diagonal_mul] at hx
 constructor; · by_contra p; have hv:i∉ X:=fun h=>p (mem_filter.mp h).2; simp only [if_neg hv,zero_mul,sub_self] at hx; exact v (by simpa using hx.symm)
 intro p; have hy:j∈X:=mem_filter.mpr ⟨mem_univ _,p⟩; rw [if_pos hy,mul_one,sub_self] at hx; exact v hx.symm
lemma painted (h:culm U=U)(hp:x=o∨y=o) :Branded o (bud_k o x y U):=by
 intro i j v; obtain ⟨p,T⟩:=gone_l o x y U _ _ v; have he:U (portB i) (portB j)≠0:=by
    intro h; apply v; unfold bud_k seed_k; simp [h,p,T,Matrix.of_apply]
 obtain ⟨u,t⟩:= slot_φ _ h _ _ he; exact ⟨mem_filter.mpr ⟨mem_univ _,u⟩,fun k=>t (mem_filter.mp k).2,p ▸ T ▸ hp⟩
lemma tap_Ψ (P:Dome)(p:Noble P):Branded o (spring_V P o):=by
 unfold spring_V; have h0:=painted o o o _ p.1.1 (Or.inl rfl); refine (brand_P _ _ _ h0 ?_).1; apply brand_S; exact fun i _=> (brand_P _ _ _ (brand_P o _ _ (painted _ _ o _ (p.1.2.1 i) (Or.inr rfl)) (painted _ _ o _ (p.1.2.1 i) (Or.inr rfl))).2 (brand_P o _ _ (painted _ _ o _ (p.1.2.2 i) (Or.inl rfl)) (painted _ _ o _ (p.1.2.2 i) (Or.inl rfl))).2).1
lemma bornT (o:Site N)(P:Op (Single N))(h:Branded o P)(V:Chin N):Branded o (ρlens P V):=by
 intro i j v; have heZ:boxM P i.1 j.1 ≠0:=by intro e; apply v; rw [show ρlens _ _ i j= _ from stride_X P i.1 j.1 V (fun _=>0) i.2 j.2,arm,e,zero_mul]; rfl
 obtain ⟨u,t,w⟩ : ∃ u v:SU.Slot, P (i.1,u) (j.1,v)≠0:=by by_contra! he; exact heZ (Matrix.ext fun x y=>he x y)
 obtain ⟨p,q,l⟩:=h (i.1,u) (j.1,t) w; exact ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2⟩,fun s=>q (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp s).2⟩),l⟩
-- Build Soak.T. price panel by norm boot.One side anchor guarantee. Vertex bounds pay_M.
variable (p q:Rock N)(d:ℝ)(h:0<d)(u:d≤1)(X:Op (Single N))
abbrev Λrod(x y:Rock N):= Font.shiftH (Cube.node x.1) (Cube.node y.1)
abbrev χrod(x y: Rock N):= Tulip.traceP (Cube.node x.1) (Λrod x y)
abbrev κfare(T:Op SU.Slot):ℝ:= ((Λrod p q).length+1:ℝ)*(1+d)^(Λrod p q).length * ‖T‖
include h u
lemma Ωg(p':MarkPH X): Suite (badge _) (bail N d) (bail N d) (χrod p q) (Tulip.reed p q (κfare p q d (boxM X p q))) (fun x:Openc (Cube.More N) d=> Φp p q X x.val):=by
 let T:= boxM X p q; let R(v:Openc (Cube.More N) d):=arm X p q v.val; let e:=node p.1; let t:=node q.1; let r:=Λrod p q; let S:=Tulip.traceP e r; have hs:stop e r=t:=stopH ..; let P':= κfare p q d T
 let H:=arm X p q; have hx: Differentiable ℂ H:=( (track_d e r).fst).const_mul T; have hp:Continuous R:=hx.continuous.comp continuous_subtype_val; have hv:(0:ℝ)≤d:= h.le
 refine Tulip.panel_ticket (p:=fun (g:Seat N→SU.E) (i:Rock N)=>matter (g (node i.1))) (q:=fun (g:Seat N→SU.E) (i: Rock N)=>matter (g (node i.1))) (fun _=>rfl) (fun _=>rfl) p q S _ R (trace_g ..) (fun _=>trace_source ..) (fun _=> show t∈ S from hs ▸ trace_last ..) ?_ (by unfold κfare; positivity) ?_ hp ?_ ?_
 · intro g z; let U:Op SU.Slot:= (matter (g e)).val; let V:Op SU.Slot:= (matter (g t)).val; have hx:T*U=U*T:= (Moto.cap_c X (g e) p' p q).eq -- tune
   let K(x:Chin N):=Tulip.track x e r; have ht:R ((forum N d).drive g z)= T*(U*(K z.val).1*star V) :=by change T*(Tulip.track (Tulip.relayg g z.val) e r).1= _; rw [show Tulip.track _ _ _= _ from Tulip.track_g g z.val e r,hs]; rfl
   rw [ht]; change T*(U*_*star V)*V=U*(T*_); rw [mul_assoc T,mul_assoc _ (star V),show star V*V=1 from (matter (g t)).property.1,mul_one,←mul_assoc T,hx, mul_assoc]
 · intro i j; apply honors (f:=fun z=> H z i j); exact (differentiable_pi.mp (differentiable_pi.mp (by exact hx) _) _).differentiableOn -- as gage
 · intro z; let V:=Tulip.track z.val e r; let A:ℝ:=(1+d)^r.length; have hl: ‖V.1‖≤ A:=(norm_fst_le _).trans (track_size d hv _ _ _ z.property); change ‖T*V.1‖≤ (r.length+1:ℝ)*(1+d)^r.length * ‖T‖; exact (norm_mul_le ..).trans (((mul_le_mul_of_nonneg_left hl (norm_nonneg _)).trans_eq (mul_comm ..)).trans (by rw [mul_assoc]; exact le_mul_of_one_le_left (mul_nonneg (by unfold A; positivity) (norm_nonneg _)) (by simp)))
 intro z y; let B:= (1+d)^r.length; let F:= fare S z.val y.val; let a:= (r.length+1:ℝ) * B; let x':= Tulip.track z.val e r; let y':=Tulip.track y.val e r; have hx':0≤B:=by unfold B; positivity
 change ‖T*x'.1-T*y'.1‖ ≤ a*‖T‖*(F/|d|); rw [←mul_sub]; have he:‖x'.1-y'.1‖ ≤ r.length*(B*F) :=(norm_fst_le (x'-y')).trans (track_vol d hv e r z.val y.val z.property y.property)
 refine (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans ?_); rw [abs_of_pos h, mul_comm a, mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); rw [←mul_assoc]; apply mul_le_mul; · unfold a; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hx'
 · exact le_div_self (fare_t ..) h u
 · exact fare_t ..
 unfold a; positivity
omit h u
lemma box_phi(p':Prism.Rock N): (∑ i:Single N,∑ j:Single N,Tulip.reed p q a i j) = (Fintype.card SU.Slot:ℝ)^2 * a:=by
 simp_rw [Fintype.sum_prod_type (α₂:=SU.Slot)]; unfold Tulip.reed; simp only [ite_and]; rw [sum_eq_single p]; swap; · intro i _ t; simp [t]
 swap; · simp
 simp only [ite_true]; have he : (∑ r:Rock N,∑ _:SU.Slot, if r=q then a else 0)=(Fintype.card SU.Slot:ℝ)*a:=by rw [sum_eq_single q]; simp; intro i _ w; simp [w]; simp
 simp_rw [he]; rw [sum_const,card_univ,nsmul_eq_mul,sq,mul_assoc]
abbrev νt(a d:ℝ)(w:ℕ):ℝ:= Real.exp (a*(w+1:ℕ))*(Fintype.card SU.Slot:ℝ)^2*((w+1:ℝ)*(1+d)^w)
end YM.CF.Swell
