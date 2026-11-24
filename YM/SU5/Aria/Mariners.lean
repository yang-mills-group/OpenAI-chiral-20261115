import YM.SU5.Aria.Euphony
import YM.Heat.Imaginary
/-! # Holomorphic time lanes for spread apertures. Re time offsets, no contacts passed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria.Helm
open Set Function Filter Metric ContinuousLinearMap OS.Semigroup
open scoped Topology BigOperators Matrix InnerProductSpace NNReal
variable {G:Hilbert}{j:Axis}(S:OS.Semigroup G j) {B I:Type*}
def phase (z:ℂ): G.Op:= (S.edge (-z.im)).comp (S.E z.re.toNNReal)
lemma insidePhase (z:ℂ)(h:0<z.re) : phase S z=S.F z:=by
 have he: z=duration z.re.toNNReal+sideways (-z.im):=by apply Complex.ext <;> simp [sideways,Real.coe_toNNReal,duration,h.le] -- tune
 unfold phase; rw [←S.roots_heat (Real.toNNReal_pos.mpr h), S.along (dur.mpr (Real.toNNReal_pos.mpr h)), ←he]
lemma standard (t:ℝ) : phase S (t:ℂ)= S.E t.toNNReal := by unfold phase; rw [Complex.ofReal_im,neg_zero,S.birth]; rfl
lemma owes_z (t:ℝ) : phase S (sideways t)=S.edge t:=by unfold phase; simp [sideways,S.eZero] -- tune
lemma phase_p (t:ℂ) : ‖phase S t‖≤ 1:=by
 unfold phase; refine (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul ?_ (S.shrinks _) (norm_nonneg _) zero_le_one).trans (one_mul _|>.le))
 exact opNorm_le_bound _ zero_le_one (fun i=> by rw [S.life,one_mul])
private lemma strongDiff [A:TopologicalSpace B](p:B→G.Op)(q:B→G)(t:Continuous q)(y:∀ x:G,Continuous (fun i=>p i x))(C:ℝ)(c:0≤C)(g:∀ i, ‖p i‖≤C) : Continuous (fun i=>p i (q i)):=continuous_iff_continuousAt.mpr fun x=> firmly p c (Eventually.of_forall g) (y _|>.continuousAt) (t.continuousAt)
lemma phase_cont(z:G): Continuous (fun t=> phase S t z):= strongDiff _ (fun t:ℂ=>S.E t.re.toNNReal z) ((S.continuousE z).comp (continuous_real_toNNReal.comp Complex.continuous_re)) (fun i=> (S.cont i).comp (Complex.continuous_im.neg)) 1 zero_le_one (fun t:ℂ=> (opNorm_le_bound (S.edge (-t.im)) zero_le_one (fun i=> by rw [S.life,one_mul])))
lemma phase_analytic {t:ℂ}(h:0<t.re): AnalyticAt ℂ (phase S) t:=by
 apply (S.localHeat _ h).congr; filter_upwards [(open_inside.mem_nhds h)] with x hx; exact (insidePhase S x hx).symm
variable (r:I→ℝ)(z:I→ℂ)(A:I→G.Op)(t:ℂ)
abbrev Toll (p:ℂ): Prop:=0 < p.re
noncomputable def crewOpera (z:I→ℂ)(L:List I) (t:ℂ): G.Op:=match L with
 | []=> id'
 | i::L=> (phase S (z i-(r i:ℂ)-t)) * A i* crewOpera z L (z i+(r i:ℂ))
where id': G.Op:=1
def Room (z:I→ℂ)(L:List I) (t:ℂ): Prop:= match L with
 | []=>True
 | i::L=> Toll (z i-(r i:ℂ)-t) ∧ Room z L (z i+(r i:ℂ))
local notation "U" z:max=> crewOpera S r A z -- argument order? `z` duplicated section variable?
#check crewOpera
lemma aesthetic [NormedAddCommGroup B][NormedSpace ℂ B](L:List I)(p:B)(F:I→B→ℂ)(f:B→ℂ)(g:Room r (fun i=>F i p) L (f p))(hf:AnalyticAt ℂ f p)(e:∀ i∈L, AnalyticAt ℂ (F i) p) : AnalyticAt ℂ (fun x:B => crewOpera S r A (fun i=>F i x) L (f x)) p:=by
 induction L generalizing f with
 | nil=> simp only [crewOpera]; exact analyticAt_const
 | cons i l ih=>
   obtain ⟨g,t⟩:=g; simp only [crewOpera]; let v:= fun x:B=>F i x+(r i:ℂ)
   have hx := e i (List.Mem.head ..); have hp := ih v t (hx.add analyticAt_const) fun j h=> e j (List.Mem.tail _ h)
   exact ((AnalyticAt.comp_of_eq (g:=phase S) (phase_analytic S g) ((hx.sub analyticAt_const).sub hf) rfl).mul analyticAt_const).mul hp
lemma crew_cont (L:List I) (x:G) : Continuous (fun y:(I→ℂ) × ℂ => crewOpera S r A y.1 L y.2 x):=by induction L with
 | nil=>exact continuous_const
 | cons i l ih=>
   let v(y:(I→ℂ)× ℂ):= crewOpera S r A y.1 l (y.1 i+(r i:ℂ)) x; let u(y:(I→ℂ) × ℂ):= y.1 i-(r i:ℂ)-y.2; have hu:Continuous u:= ((continuous_apply i).comp continuous_fst |>.sub continuous_const).sub continuous_snd
   have hv:Continuous v:= ih.comp (f:=fun y:(I→ℂ) × ℂ => (y.1,y.1 i+(r i:ℂ))) (continuous_fst.prodMk (((continuous_apply i).comp continuous_fst).add continuous_const))
   exact strongDiff (fun x=> phase S (u x)) (fun y=> A i (v y)) ((A i).continuous.comp hv) (fun i=>(phase_cont S i).comp hu) 1 zero_le_one (fun _=> phase_p ..)
lemma pays_edge (u:I→ℝ)(p:ℝ)(L:List I): crewOpera S r A (fun i=>(↑(u i):ℂ)) L (p:ℂ)= rector S A (fun i=> u i-r i) (fun i=> u i+r i) L p:=by
 induction L generalizing p with
 | nil=>rfl
 | cons i l ih=> rw [crewOpera,rector,←Complex.ofReal_sub,←Complex.ofReal_sub,← Complex.ofReal_add,ih,standard]; rfl
-- explicit edge price Mink-translations with arbitrary real Mink time difference per seam and no heat gap
noncomputable def trade (u:I→ℝ)(L:List I)(p:ℝ): G.Op:= match L with
 | []=> 1
 | i::L=> ((S.edge (u i-p)).comp (A i)).comp (trade u L (u i))
def touch (s:I→ℝ): List I→ ℝ→ Prop
 | [],_=> True
 | i::L,b=> s i-r i=b ∧ touch s L (s i+r i)
lemma trades (v u:I→ℝ)(p b:ℝ)(L:List I)(h:touch r u L b):
    crewOpera S r A (fun i=> (u i:ℂ) + sideways (v i)) L ((b:ℂ)+sideways p)=trade S A v L p:=by
 induction L generalizing p b with
 | nil=>rfl
 | cons i l ih=>
   obtain ⟨a,h⟩:= h
   unfold trade; rw [crewOpera]; rw [show (u i:ℂ)+_-(r i:ℂ)-((b:ℂ)+sideways p)=sideways (v i-p) from ?_,owes_z,add_right_comm (u i:ℂ) (sideways (v i)),← Complex.ofReal_add,ih _ _ h]; rfl
   · rw [←a]; unfold sideways; push_cast; ring
abbrev threshold (z:I→ℂ)(k:I): ℝ:= (z k).re-r k
abbrev expense (z:I→ℂ)(k:I): ℝ:= (z k).re+r k
lemma room_clock (L:List I) : Room r z L t ↔ Sheet (threshold r z) (expense r z) L t.re:=by
 induction L generalizing t with
 | nil=>rfl
 | cons i l ih=> rw [Room,Sheet,ih]; unfold threshold expense Toll; simp
lemma sheet_rank (p s:I→ℝ)(L:List I)(b:ℝ)(j:Sheet p s L b)(u:∀ i∈ L,p i≤ s i): L.Pairwise (fun i k=> s i<p k) ∧ ∀ i∈ L,b<p i:=by
 induction L generalizing b with
 | nil=> exact ⟨List.Pairwise.nil,by simp⟩
 | cons i l ih=>
   obtain ⟨t,j⟩:=j; obtain ⟨a,b⟩:=ih (s i) j (fun y v=>u y (List.Mem.tail _ v)) -- shadow b!
   refine ⟨List.pairwise_cons.mpr ⟨fun i t=>b i t,a⟩,fun x p=>?_⟩; rcases List.mem_cons.mp p with rfl|v; exact t; exact (t.trans_le (u _ (List.Mem.head ..))).trans (b x v)
-- touch path
abbrev Lane (s:I→ℝ)(v:I→ℝ)(p u:ℝ): (I→ℂ) × ℂ:= (fun i=> (s i:ℂ)+sideways (v i), (p:ℂ)+sideways u)
lemma convexRide (V:I→ℝ)(s w: ℝ)(i:List I)(y:ℂ)(z:I→ℂ)(h:touch r V i s)(u:Room r z i y)(L:I→ℂ)(t:ℂ)(p:∀ j∈i,(L j).re=(V j)): (t.re=s)→ 0<w→ Room r (fun j=> L j+(w:ℂ)*(z j-L j)) i (t+(w:ℂ)*(y-t)):=by
 intro W g; induction i generalizing y s t with
 | nil=> trivial
 | cons i l ih=>
    let F (j:I):= L j+(w:ℂ)*(z j-L j); obtain ⟨b,h⟩:=h; obtain ⟨c,u⟩:=u;
    have Y:=p i (List.Mem.head ..)
    constructor
    · unfold Toll at *; simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,W,Y] at *; nlinarith
    specialize ih (V i+r i) (z i+(r i:ℂ)) h u (L i+(r i:ℂ)) (fun i v=> p i (List.Mem.tail _ v)) (by simp [Y]); convert ih using 1; ring
lemma at_boundary (s v: I→ℝ)(p u:ℝ)(L:List I)(h:touch r s L p)(X:Room r z L t): (Lane s v p u)∈closure {a:(I→ℂ) × ℂ|Room r a.1 L a.2}:=by
 let A:= Lane s v p u; let B: (I→ℂ) × ℂ:= (z,t); let f (x:ℕ):ℝ:=(1/2)^x; let g(n:ℕ):=A+(f n:ℂ) • (B-A); have ht:=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num:(0:ℝ)≤1/2) (by norm_num:(1/2:ℝ)<1); have he:Tendsto (fun n=>(f n:ℂ)) atTop (𝓝 0):= by simpa [f] using ht.ofReal
 have hp:Tendsto g atTop (𝓝 A):=by simpa [g] using (tendsto_const_nhds (x:=A)).add (he.smul (tendsto_const_nhds (x:=B-A)))
 exact mem_closure_of_tendsto hp (Eventually.of_forall fun n=>convexRide r s p (f n) L t z h X A.1 A.2 (fun i _=>by change ((s i:ℂ)+sideways (v i)).re=_; simp) (by change ((p:ℂ)+sideways u).re=_; simp) (by unfold f; positivity)) -- maybe ofReal lemma
end YM.CF.Buffered.Afterglow.Tower.Aria.Helm
#print axioms YM.CF.Buffered.Afterglow.Tower.Aria.Helm.at_boundary
