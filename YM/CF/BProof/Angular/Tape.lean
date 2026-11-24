import YM.CF.BProof.Law.Flat
import YM.CF.BProof.Angular.Signs

/-! Full assembly of the angular factors after axial change. The tape uses density
before restricting labels. It remains a normalized conditional rule for noise even if labels
are rejected. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular.Yard
open Function Lattice Gauge Mag CF.BProof.Face SU MeasureTheory Wilson Finset Filter Law RG
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s: Side}(Y:Yard s)(i:Y.Index)(y:ℝ)(S:Hall s)(U:Config G s)

abbrev FaceS := Y.Index → Eyes s
abbrev Glyph := Y.Index → Signs s
def accepted (p:Y.Glyph) : Prop := ∀ i:Y.Index, if Y.D i then p i=0 else p i∈ wages (Y.u i) Y.long y S U
def sweepLabel (p:Y.Glyph) : Y.FaceS := fun i=> if Y.D i then 1 else peeks (Y.u i) Y.long y S U (p i)
lemma front_owned {i:Y.Index} (h:¬Y.D i)(b:Bool)(p:Space s)(j:TAxis) : horiz (front (Y.u i) Y.long b) p j ∈Y.field:= by
 rw [← gFrame Y i b h]; let z:=Y.location i b; rw [noPay Y z _ _ (p:=p) (j:=j)]; rw [← atD_full Y z]; rw [depth_at _ _ le_rfl]; exact Y.short_pos; exact Y.nEnd_mem z -- tune
lemma accepted_m (p:Y.Glyph) : MeasurableSet {U:Config G s | Y.accepted y S U p}:=by
 unfold accepted; simp only [Set.setOf_forall]; apply MeasurableSet.iInter; intro i; split_ifs with h; by_cases g:p i=0<;>simp [g]; exact wage_m ..
lemma sweepLabel_m (p:Y.Glyph) : Measurable (fun U:Config G s=> Y.sweepLabel y S U p):=by
 apply measurable_pi_lambda; intro i; unfold sweepLabel; split_ifs; exact measurable_const; exact peek_m ..
lemma sweeps_eq {W:Config G s} (e:Set.EqOn U W (↑Y.field))(h:¬Y.D i)(b:Bool) : inlet (Y.u i) Y.long U b=inlet (Y.u i) Y.long W b := by
 ext1 ⟨p,j⟩; exact e (front_owned Y h b p j)
lemma sweepLabel_eq {W:Config G s}(e:Set.EqOn U W ↑Y.field) (p:Y.Glyph) : Y.sweepLabel y S U p=Y.sweepLabel y S W p:=by
 ext1 i; unfold sweepLabel; split_ifs with g; rfl; ext1 b; ext1 x; unfold peeks; rw [Y.sweeps_eq i U e g b]
lemma accepted_eq {W:Config G s}(e:Set.EqOn U W ↑Y.field) (p:Y.Glyph) : Y.accepted y S U p=Y.accepted y S W p:=by
 apply propext; apply forall_congr'; intro i; split_ifs with g; rfl
 rw [wages_mem,wages_mem]; unfold lifts; apply forall_congr'; intro b; unfold peeks; rw [Y.sweeps_eq i U e g b]

variable (f:Y.FaceS)
/-- after squashing these carry the face gauges only. -/
def high (b:Site s) := sight (Y.u i) Y.long S U (f i) (flag (Y.u i) (time b) Y.long) (space b)
def baseN := Lattice.gauge (Y.high i S U f)⁻¹ (formal (Y.u i) Y.long S U (f i))
def slot (p:Bond s) := if Y.D i then mag y p else Y.baseN i S U f p
def root (p:Bond s):= Y.twinsBand (time p.1)
lemma baseN_eq (W:Config G s)(e:Set.EqOn U W ↑Y.field) (h:¬Y.D i): Y.baseN i S U f=Y.baseN i S W f:=by
 have hh(b:Bool) := Y.sweeps_eq i U e h b
 unfold baseN; ext1 p; unfold Lattice.gauge; simp only [Pi.inv_apply]; unfold formal light outlook high sight; simp_rw [hh]
lemma high_fit (h:Y.Flat U)(hx:¬Y.D i): Set.EqOn (Y.high i S U f) (V (Y.u i) Y.long S U (f i)) ↑(Y.band i):=by
 intro x hg; have he:= stage_identity (Y.u i) Y.long U (Y.long_lt.trans Y.count_lt) (fun v p hv hh=> h (Y.trunk_b p hx hv hh)) hg; unfold high V; nth_rw 1 [stage_layers]; rw [he,Pi.one_apply,mul_one]
lemma high_price (h:Y.Flat U)(hx:¬Y.D i)(p:Bond s)(hp:p∈washes (Y.u i) Y.long) : density G (xi y) (Y.baseN i S U f p) (U p)=density G (xi y) (formal (Y.u i) Y.long S U (f i) p) (hall (Y.u i) Y.long S U (f i) p) := by
 let t:=Y.high i S U f; let a:=p.1; let b:=p.1+step p.2; obtain ⟨hp,hq⟩:= (mem_wash ..).1 hp
 let l:= formal (Y.u i) Y.long S U (f i) p; have hv:hall (Y.u i) Y.long S U (f i) p=t a*U p*(t b)⁻¹:=by unfold hall Lattice.gauge; rw [← high_fit Y i S U f h hx hp,← high_fit Y i S U f h hx hq]
 rw [hv]; have ht:= density_both G (Y.baseN i S U f p) (U p) (xi y) (a:=t a) (b:=(t b)⁻¹); rw [show t a*Y.baseN i S U f p*(t b)⁻¹=l from ?_] at ht; exact ht.symm
 change t a*((t a)⁻¹*l*((t b)⁻¹)⁻¹)*(t b)⁻¹=l; group

/-- center to be used on each link (rent only). -/
def centers (p:Bond s) := Y.slot (Y.root p) y S U f p
def toll := if Y.D i then shut (Y.u i) Y.long y U else stream (Y.u i) Y.long y S U (f i)
def owed := ∏ i:Y.Index,Y.toll i y S U f
lemma rents_root (p:Bond s)(hp:p∈Y.leases i) : Y.root p=i:= u_part Y i _ (mem_strip.mp (Y.leases_w i hp).1)
lemma price (h:Y.Flat U) : Y.owed y S U f = ∏ p∈Y.rent,density G (xi y) (Y.centers y S U f p) (U p):=by
 rw [rent,prod_biUnion]; swap
 · intro i hi j hj e; apply disjoint_left.mpr; intro p hp hq; exact e (Y.leases_dist hp hq)
 unfold owed; refine prod_congr rfl fun i hi=>?_
 rw [show (∏ p∈ Y.leases i,density G (xi y) (Y.centers y S U f p) (U p)) = ∏ p∈ Y.leases i,density G (xi y) (Y.slot i y S U f p) (U p) from prod_congr rfl fun p hp=> by unfold centers; rw [Y.rents_root i p hp]]; unfold toll slot leases; split_ifs with H; rfl; exact prod_congr rfl fun p hp=> (high_price Y i y S U f h H p (by exact filter_subset _ _ hp)).symm
lemma centers_eq (W:Config G s)(e:Set.EqOn U W ↑Y.field): Y.centers y S U f=Y.centers y S W f:=by ext1 p; unfold centers slot; split_ifs with h; rfl; rw [baseN_eq Y _ S U f W e h]
lemma high_m : Measurable (Function.uncurry (Y.high i S)):=by
 let t (x:Config G s × Y.FaceS) := (x.1,x.2 i); have h:Measurable t:=by unfold t; fun_prop
 let Q:= Function.uncurry (sight (Y.u i) Y.long S); have he : Measurable (Q ∘ t):= (sight_m ..).comp h
 apply measurable_pi_lambda; intro x; exact (measurable_pi_apply (X:=fun _:Space s=> E) (space x)).comp ((measurable_pi_apply (X:=fun _:Bool=>Frame s) (flag (Y.u i) (time x) Y.long)).comp he)
lemma centers_m : Measurable (Function.uncurry (Y.centers y S)):=by
 apply measurable_pi_lambda; intro p; set P:=Y.root p; unfold Function.uncurry centers slot; split
 · exact measurable_const
 let F(a : Config G s × Y.FaceS):= (a.1,a.2 P); have hf:Measurable F:=by unfold F; fun_prop
 let q := Function.uncurry (formal (Y.u P) Y.long S); have hg:Measurable (q∘ F):= (formal_m ..).comp hf
 have e (x:Site s):= (measurable_pi_apply (X:=fun _:Site s=> E) x).comp (high_m Y P S)
 exact (((e p.1).inv).mul ((measurable_pi_apply (X:=fun _ : Bond s=> E) p).comp hg)).mul ((e (p.1+ Lattice.step p.2)).inv.inv)
lemma toll_pay (hx:xi y≤1):0≤Y.toll i y S U f ∧ Y.toll i y S U f≤ ((4/xi y)^matDim G)^((Y.long+1)*s.val^3*4):= by
 unfold toll; split
 · exact pay_density (Y.u i) Y.long y (washes (Y.u i) Y.long) (mag y) U (fun x h=>h) hx (Y.long_lt.trans Y.count_lt)
 exact pay_density (Y.u i) Y.long y (watches (Y.u i) Y.long) (formal (Y.u i) Y.long S U (f i)) (hall (Y.u i) Y.long S U (f i)) (filter_subset ..) hx (Y.long_lt.trans Y.count_lt)
lemma toll_m : Measurable (Function.uncurry (Y.toll i y S)):=by
 let F(p:Config G s × Y.FaceS):=(p.1,p.2 i); have hF:Measurable F:=by unfold F; fun_prop
 unfold toll Function.uncurry; split_ifs
 · change Measurable (shut (Y.u i) Y.long y ∘ (Prod.fst : Config G s × Y.FaceS→Config G s)); exact (shut_m (Y.u i) Y.long y).comp measurable_fst
 change Measurable ((Function.uncurry (stream (Y.u i) Y.long y S)) ∘ F)
 exact (stream_m (Y.u i) Y.long y S).comp hF
lemma toll_env (hx:xi y≤1): Envelope (Function.uncurry (Y.toll i y S)):=⟨toll_m Y i y S,_,fun x=> (Real.norm_of_nonneg (toll_pay Y i y S x.1 x.2 hx).1).trans_le (toll_pay Y i y S x.1 x.2 hx).2⟩
lemma owed_env (hx:xi y≤1): Envelope (Function.uncurry (Y.owed y S)):=by
 let F(x:Y.Index)(p:Config G s× Y.FaceS):= Y.toll x y S p.1 p.2; change Envelope (fun p=>∏ i,F i p); generalize he:(univ:Finset Y.Index)=t; clear he; induction t using Finset.induction_on with|empty=> simp; exact Envelope.const 1|insert i s h ih=> simp_rw [prod_insert h]; apply Envelope.mul _ ih; exact toll_env Y i y S hx
end YM.CF.BProof.Angular.Yard
