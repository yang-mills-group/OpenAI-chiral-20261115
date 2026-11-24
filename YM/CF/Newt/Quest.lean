import YM.CF.Newt.Stage
import YM.Push.STATIONARY_UNIFORM.Continue
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ E: Type} [NormedAddCommGroup E][NormedSpace ℝ E] [Fintype ι] [Fintype τ] {C D v K d N X U s r a e:ℝ}{n l:ℕ}
open Next.SectorChange (panels shots)
open Next.SectorChange.Rows (gram)
variable {G:Gauge}{P:Patch}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
lemma decrease {x:Mast G c}(L:Mast G c→L[ℝ] Mast G c)(Q: Fish ι→L[ℝ] Fish τ)(LINK:Fish ι→L[ℝ] Fish τ)(z:Mast G c→ Fish τ→L[ℝ] Fish τ)(h:1≤n)(hz:∀ v, ‖v‖<r→Allows n z v C)(ha:‖x‖≤1)(hs:0≤s)(ht:s≤1)(hm:s<r)(hq:‖Q‖ ≤ N)(q: Allows n (fun _: Mast G c=> ((z 0).comp Q-LINK)) x (D*s)):
 Allows n (fun u=>(z (s•u)).comp Q-LINK) x ((2^n * C * N+D)*s):=by -- tune bind LINK
 have he := fiction (near_s hs ht h hm hz ha) (allows_const (n:=n) x hq); have hv:=he.add q
 refine (hv.mono (le_of_eq (by ring))).germ (Eventually.of_forall fun i=>?_); ext1 j; simp
-- delayed preparation. δ from tax widths.
lemma mat_paid (T:Teller G)(P:Patch)(n:ℕ)(hn:3≤n) (W:Before G T.top.width T.top.paths T.j T.bind n):
 let p:=W.tables T.top.clip P
 ∃ B v C:ℝ,0<B∧0<v ∧0<C ∧∀ {c f:Side}(S:StepData c f)(U:Tube G S)(x:ℝ), Cert P T S U x → B=p.initial ∧ p.horizon>0 ∧ v=p.width∧∀ (F:Forest S.ratio)(k:S.Choices),
 Uniform.Receipt (Uniform.address F G) p.width n p.coords p.value p.initial p.gap (costP F k U.high U.up) ∧ ∀ z:Positions (Uniform.Joint F G), ‖z‖<B→ Wax (costP F k U.high U.up) z n v C :=by
 intro p; let C:=max p.value 1; have hC:0<C:=lt_of_lt_of_le zero_lt_one (le_max_right ..)
 refine ⟨if 0<p.initial then p.initial else 1,if 0<p.width then p.width else 1,C,by split; assumption; exact zero_lt_one,by split; assumption; exact zero_lt_one,hC,?_⟩
 intro c f S U x h; have hT:= h.funds.1; obtain ⟨a,b,hx,hz⟩:=hT.feeds
 letI : Nonempty (Forest S.ratio):=Tree.select _ S.patch.odd_side; let F:= Classical.arbitrary (Forest S.ratio); let k:=Classical.arbitrary S.Choices
 have H (F:Forest S.ratio)(k:S.Choices): Uniform.Receipt (Uniform.address F G) p.width n p.coords p.value p.initial p.gap (costP F k U.high U.up):=by
    unfold p; rw [← h.got, hT.high]; exact (W.receipt F k hx h.pace hT.atStep hT.knobs).1
 have hp:=H F k; have hm:=hp.pos_a; have hv:=hp.pos_r
 rw [if_pos hm,if_pos hv]; exact ⟨rfl,hp.reserveX_pos,rfl,fun F k=> ⟨H F k,fun z hp=> by obtain ⟨ht,hb⟩:=(H F k).born z (mem_ball_zero_iff.mpr hp); exact ⟨ht,hb.mono (le_max_left ..)⟩⟩⟩
-- prepare Φ chart. true-cut orientation same. β.
lemma rentsD {P:Patch} (K:Teller G)(h:P.Branches K.bind G)(n j:ℕ)(hp:1 ≤ n) (W:Before G K.top.width K.top.paths K.j K.bind (n+1+1)):
 ∃ r C D b:ℝ,0<r∧0<C∧0<D∧0<b∧
 ∀ᶠ x:ℝ in atTop, ∀{c f:Side}(S:StepData c f)(U:Tube G S), Cert P K S U x→∀ (F:Forest S.ratio)(k:S.Choices),
 let y:=W.tables K.top.clip P
 let J:=costP F k U.high U.up; let J':= costP F k U.high (grainA U.up (Stores.till x)); let P₁:=gall U x k F
 Uniform.Receipt (Uniform.address F G) y.width (n+1+1) y.coords y.value y.initial y.gap J ∧∀ s:ℝ,0<s→temp x≤s→s≤b→ Clinic n C D s r J J' (fun i=>P₁ (s•i)) j:=by
 obtain ⟨B,v,C,hB,hv,hC,g⟩:= mat_paid K P (n+1+1) (by omega) W
 obtain ⟨R,D,hR,hD,H⟩:= moon K n P h
 let r:= min B 1; let b:=min (min R r /2) 1; have hr :0<r:= lt_min hB zero_lt_one; have hb : 0<b:=lt_min (half_pos (lt_min hR hr)) zero_lt_one
 let d:=tailP P K.top.width (n+1); have hd:0<d:=by have hm:= Uniform.width_positive K.top.width_pos (n+1) P.L; unfold d tailP Uniform.weaker; have:=Uniform.width_positive (half_pos K.top.width_pos) (n+1) P.L; positivity
 obtain ⟨Z,hZ⟩:=Uniform.paint_supply G (n+1)
 let B0(a:ℝ):=1+Uniform.townCost G*Uniform.countCost a; let E:=B0 d^(n+1); let M:=C*B0 v^(n+1); let Q:= (2^n*M*D+(1+D))
 have he(v:ℝ)(p:0<v):1≤B0 v:= le_add_of_nonneg_right (mul_nonneg (by positivity) (Uniform.count_pos p).le)
 have hE:= he d hd; have hY:= he v hv; have hM:0<M:= by unfold M; positivity
 let R':= M+E+Q; have hQ:0≤Q:=by unfold Q; positivity
 have hE0 :0 ≤ E:=by unfold E; positivity
 have hk:M ≤ R':=by unfold R'; linarith
 let p:=W.tables K.top.clip P
 let V:=muskP G (n+1) Z (K.top.width) K.top.paths P.L
 let J:=composeCost n D 1; have hJ:0<J:= by unfold J composeCost; positivity
 refine ⟨r,R',J,b,hr,hM.trans_le hk,hJ,hb,?_⟩
 filter_upwards [H,smallF (n:=j) (half_pos K.top.width_pos) (|V|), eventually_gt_atTop (0:ℝ)] with x H hx he
 intro c f S U ht F k p JH J' P'
 obtain ⟨hr₁,hr₂⟩ := H S U ht F k; obtain ⟨hv1,hv2,hP,G0⟩:=g S U x ht
 obtain ⟨he0,hf⟩:=G0 F k; have hx1 (y) (hy:‖y‖<r) := hf y (hy.trans_le (min_le_left ..)); have hm: ‖paintO (block JH 0)‖≤M := (stiffness (x:=0) (hx1 0 (by simpa)).hv (hx1 0 (by simpa)).he (Uniform.town F) hC.le hv).value -- tune
 refine ⟨he0,fun s hs he' hX=>?_⟩; have hL:s<R:=lt_of_le_of_lt (hX.trans (min_le_left ..)) (lt_of_lt_of_le (half_lt_self (lt_min hR hr)) (min_le_left ..)); have hs':= hX.trans (min_le_right _ 1) -- wrong
 refine ⟨hM.trans_le hk,hJ,fun {y} hy=> ⟨(hx1 _ hy).he,(stiffness (hx1 _ hy).hv (hx1 _ hy).he (Uniform.town F) hC.le hv).mono hk⟩, fun {z} hz=>?_,fun {x'} ht' => ?_, fun {y} hy=>?_⟩
 · have he :=ht.funds.1; obtain ⟨Λ,Q,hv,hi⟩:= he.feeds; let R:=Stores.till x
   have hx' y(hy:‖y‖<r):Wax (JH-J') y (n+1) d (s^j):=by
      have hh:= tail_paid (R:=U.up) (σ:=K.top.width) (q:=U.high) (he.high.symm ▸ hv) R F k hZ y (mem_ball_zero_iff.mpr (hy.trans_le (min_le_right ..)))
      have hY:= hh; rw [ht.got] at hh -- dependent rewrite?
      apply hh.mono; let t:= tollE K.top.width R
      exact (mul_le_mul_of_nonneg_left (le_abs_self _) (show 0 ≤ t from (Real.exp_pos _).le)).trans (hx.trans (pow_le_pow_left₀ (Work.E04.temp_nonneg x) he' _))
   have h:=hx' z hz
   have hLT := pin h.hv h.he (Uniform.town F) (pow_nonneg hs.le _) hd
   have hv:= hLT.smul (-1)
   simp only [abs_neg, abs_one, one_mul,neg_one_smul] at hv
   apply (hv.mono ?_).germ
   · filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with i hi
     let y:= i; have hl := mem_ball_zero_iff.mp hi
     have HE:=hx' i hl; have hw:=hx1 i hl
     have hb : DifferentiableAt ℝ JH i:= hw.he.differentiableAt (by simp)
     have hh : DifferentiableAt ℝ J' i:=by rw [← sub_sub_cancel JH J']; exact (hb.sub (HE.he.differentiableAt (by simp)))
     ext j; change -Slope (JH-J') i j= Slope J' i j - Slope JH i j
     simp only [Slope,Uniform.entry,iteratedFDeriv_one_apply,fderiv_sub hb hh,_root_.sub_apply,neg_sub]
   let L:= B0 d; change s^j* L^n ≤ _
   rw [mul_comm]; refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hs.le _); have ht : L^n≤E:=pow_le_pow_right₀ hE (by omega)
   unfold R'; exact ht.trans (le_trans (le_add_of_nonneg_left hM.le) (le_add_of_nonneg_right hQ))
 · let L:= s • ContinuousLinearMap.id ℝ (Mast G c); have hl: ‖L‖ ≤ 1:=(pole0 s _ ℝ hs.le).trans hs'; have hg:‖L x'‖≤s:= ((L.le_opNorm x').trans ((mul_le_of_le_one_right (norm_nonneg _) ht'.le).trans (pole0 s _ ℝ hs.le)))
   exact (hr₁ _ (hg.trans hL.le)).comp (f:= L) (allows_linear (L:=L) hl (hg.trans hs'))
 · let L:=paintO (block JH 0)
   have hh:Allows n (fun _: Mast G c=>(P' 0).comp L-ContinuousLinearMap.id ℝ _) y ((1+D)*s):=allows_const y (by rw [norm_sub_rev]; exact hr₂.trans (mul_le_mul_of_nonneg_left he' (by positivity)))
   have hb:= (decrease (ContinuousLinearMap.id ℝ _) L (ContinuousLinearMap.id ℝ _) P' hp (fun i hi=> hr₁ _ hi.le) hy.le hs.le hs' hL hm hh).smul (-1)
   simp_rw [abs_neg,abs_one,one_mul,neg_one_smul,neg_sub] at hb
   refine hb.mono (mul_le_mul_of_nonneg_right ?_ hs.le); unfold R' Q; rw [mul_right_comm]; linarith
end YM.CF.Newt
