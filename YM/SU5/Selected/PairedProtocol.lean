import YM.SU5.Selected.Substantive
/-! # Paired wine protocol. Variant of `Vintage.wineGod` (proofs adapted from there).
Extend coeval assertion to unaveraged lift and doubled norm bound. -/

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner
local notation "κI" i:max s:max k:max => (gram Y s i k).J.M
local notation "SN" i:max s:max => Papal.count Y s i
private lemma tenderG(s i k:ℕ)(f:Ferry Y s i k): Twosome (tent Y H) (Papal.count Y s i) (solder Y i k f.depth s):=by
 let m:=momentm Y i s; let K₀:=tent Y H; let X:=collector Y H i k f.depth s; let F:=solder Y i k f.depth s; have ht:=boxprice Y H i k f.depth s f.fire f.enters
 apply across K₀ m F (terrain Y H (Y.ir i) s) (Y:=X) (fun x=>rfl); exact fun a z _ p=>Metered.twiceX ht a z p
where across (K:Calibration)(m:Side){n:Side} (X:Mark n→ℂ)(p:K.c m=n){Y:Mark (K.c m)→ℂ}(h:∀ f,Y f=X (p▸f)) (g:Twosome K (K.c m) Y):Twosome K n X:=by subst n; rw [show X=Y from Eq.symm (funext h)]; exact g
def innerRate (d:ℕ) : ℝ:= innerRatio d/6^4
lemma innerRate_pos (d:ℕ):0< innerRate d:=div_pos (innerRatio_pos d) (by norm_num)
lemma cost_width (g:w+d+1≤ q)(h:l ≤ q) : ((4*((12*payout d q w)+l):ℕ)^4:ℝ)*innerRate d ≤ ((q^4:ℕ):ℝ):=by
 let a:=4*(2*payout d q w+l); let b:=4*(12*payout d q w+l)
 have h₀:b ≤ 6*a:=by unfold a b; omega
 refine (width_cost g h).trans' ?_
 change (b:ℝ)^4 * innerRate d ≤ (a:ℝ)^4 * innerRatio d
 rw [innerRate,← mul_div_assoc,div_le_iff₀ (by norm_num)]
 have he:(b:ℝ)^4≤ 6^4*(a:ℝ)^4:=by rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); exact_mod_cast h₀
 calc
   _ ≤ _ := mul_le_mul_of_nonneg_right he (innerRatio_pos d).le
   _ = _ := by ring

private lemma moodPair (q d w l:ℕ)(p:0<q)(r:l ≤ q)(f:w+d+1≤q)(u:ℕ)(n:Side)(g:(More n).val^4 ≤ u*(4*(12*payout d q w+l))^4):
    (↑(u*q^4):ℝ)≥ innerRate d * sites n:=by
 let ν:=4*(12*payout d q w+l); let K:ℕ:=u*(ν^4); have hp:sites n ≤ K:= by unfold sites; exact_mod_cast g
 have ht:= cost_width f r; apply (mul_le_mul_of_nonneg_left hp (innerRate_pos d).le).trans
 change innerRate d*(↑(u*ν^4):ℝ) ≤ _; push_cast; change ((4*(12*payout d q w+l):ℕ):ℝ)^4*_ ≤_ at ht -- stmt
 nlinarith only [mul_le_mul_of_nonneg_left (show (ν:ℝ)^4*innerRate d ≤ (q:ℝ)^4 from ht.trans_eq (by push_cast; rfl)) (Nat.cast_nonneg (α:=ℝ) u)] -- push_cast ν becomes sum!

lemma pairPrice {n:Side}{f:Mark n}{u:ℝ} (h: ∀ x, ‖f x‖ ≤ u)(j:Axis) (x:Fields n) : ‖reflMark j 0 f x‖ ≤ u:=by rw [reflMark,Fock.theta,twist_norm,Scroll.norm_cc]; exact h _
lemma winePair {A T:ℝ}
    (m:h ≤ P.h)(v:Inflation A P)(Z:δ≥ P.d)
    (Ft:∀ᶠ n:ℕ in atTop,∀ (N:Side),n≤N.val→Winter P.K.j δ N γ w ε ∧ ∀ M:Tulip.Male,∀ b S,Sparse d S→ HearthB R (sp b P.K.j M (1:Pane N)) S)
    (c:0 < γ)(Q:ε*R ≤ 1/3)(t': ε*(2*R+4*R*R)≤e^3)(hp:0<e)(vz:e ≤ 1)(pr:h=e⁻¹)
    (g0: 0≤a)(uz:e*(2*R+3)≤ Real.exp (-2*(a+R)))(vT:a*innerRate d ≥ T)(g: sealPrice P.V P.W - T+ blossom P.K+(A+1) ≤ -10000)(pR:0<R)
    (hq:0<q)(gq:(w+d+1) ≤ q)(vq:addgap (tent Y H)≤q) :
    ∀ᶠ s in atTop,∀ᶠ i in atTop, ∀ᶠ k in atTop,(Y.voyage i).kick≤k ∧ s ≤ Y.uv k ∧ (∀ b (S:Finset (Seat (Papal.count Y s i))), Sparse d S→HearthB R (sp b P.K.j (gram Y s i k).J.M (1:Pane (Papal.count Y s i))) S) ∧ ∀ (z:SU.Slot),
      let x:=grain (payout d q w); let F:=taggin Y s i k q d w x z; let ℓ:=max P.J.n (payout d q w+1)
      Cliplet.Perron P.K.j (gram Y s i k).J.M w d ℓ γ (gram Y s i k).p.threshold F ∧
      (∀ X:Fields _,‖F.frame X‖≤(1+R)^(q^4)) ∧ ‖Journey.compass Y i k s (reflMark 0 0 F.frame * F.frame)‖ ≤1/4096:=by
 subst h
 let B:=payout d q w; let ℓ:= max P.J.n (B+1); let I₀:=(4*(ℓ+ℓ+1)^4*q^4:ℕ); let κ:= (a+R)*(I₀:ℝ); have hm:0<B:= by unfold B payout; omega; -- omega due nonlinear count? +1
 obtain ⟨τ0,hτ,u⟩:= stampG_price B γ c; let x:= hat P.R.L P.x; let V(s i k):=(gram Y s i k); have hx:Tendsto (fun s:ℕ=>temp (x s)) atTop (𝓝 0):= (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 let H':=tent Y H; let J:=addgap H'
 obtain ⟨n,hK⟩:=Ft.exists; obtain ⟨n',un⟩:= flatAcross P.K.j (P.kJ ▸ (by decide))
 filter_upwards [measured Y v (inv_pos.mpr hp |>.le) m κ, hx.eventually (ge_mem_nhds hτ),hx.eventually (ge_mem_nhds P.J.ht)] with s hZ xZ xP
 let E:= n+n'+2*(B+1)+12*B+J+4*(2*(d+1)*q)+1
 filter_upwards [hZ,(count_grows Y s).eventually_ge_atTop E] with i gV eI
 let Ns:=Papal.count Y s i; let N₁:= (More Ns).val; have hv: E ≤ Ns.val:=eI; have hi:N₁=Ns.val*2:=rfl
 obtain ⟨F₀,F₁⟩:= hK Ns (by omega)
 let W:Seat Ns→ℕ:=fun _=>0
 have hU (k):Sparkle Ns P.d (κI i s k) P.K.j := P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _
 let D:=(1+R)^((More Ns).val^4*(q^4))
 let G:= Real.exp (-10000*sites Ns)/D; have hg:0<D:= by unfold D; positivity
 filter_upwards [ferry_later Y s i, thaw_plot Y G (by unfold G; positivity) s] with k S φ
 let X₀:=Journey.compass Y i k s; let Y₀:= solder Y i k S.depth s
 have hn:StageTw H' Y₀ P.K.j R d (κI i s k):= ⟨tenderG Y H s i k S, un Ns (by omega) _,F₁ _⟩ -- F₁ s b?
 let MU:= κI i s k; let th:=(gram Y s i k).p.threshold; have he: th=temp (x s):= ((congrArg BudgetPoint.threshold (prices_plot Y s i k S.enters).1).trans (Y.meter.boot s).1); have hχ(i):IsStarProjection (sp i P.K.j MU (1:Pane Ns)):=raft i ((hU k).projection 1 (guard0 P.dpos.le))
 refine ⟨S.depth,S.enters,F₁ (κI i s k),fun z=>?_⟩
 let o:=grain B
 let F:= taggin Y s i k q d w o z; let O:= wrap (More Ns) (Lifted.nodeC o); have heQ:F.broad=BlockP B O:=rfl
 let V':= VolumeX ((wrap Ns) ∘ booty o d q)
 obtain ⟨u',t,w'⟩:= feast (n:=Ns) (d:=d) (q:=q) (by omega) o w
 have hf:Cliplet.Perron P.K.j MU w d ℓ γ th F:= by
    apply repastPrize (p:= (show Sparse d V' from t)) (d:=(show Injective F.birth from u')) (g:=w') (w:=le_max_right ..); -- D want
    exact fun V=>u th (gram Y s i k).p.threshold_pos.le (he ▸ xZ) (by omega) (le_max_right ..) O V
 have hy:12*B+addgap (tent Y H) ≤ Ns.val:=by change 12*B+J ≤_; omega
 have hr:0<q^4:=pow_pos hq _
 have uB:addgap (tent Y H) ≤ B:=by
    refine vq.trans ?_
    unfold B payout
    apply (Nat.le_add_right ..).trans' (Nat.le_mul_of_pos_left _ (by omega))
 obtain ⟨r,L,l,v',len,p4,hL,YX⟩:= hn.doubles (terrain Y H (Y.ir i) s).symm uB hy 0 F hf rfl
 have hrQ: r ≤ L.length:= by omega
 let D':=reflMark 0 0 F.frame * F.frame
 let Vc:= CF.Pannier.Chancel.Cliplet.probe L -- qualified alias
 have hQ(k):Sea (Fock.cutM (Tset (SN i k))) (mateK _):=by rw [←touchP]; exact tickB ..
 have hCap: Backlog Y s i k e⁻¹ T κ Vc:=by
    intro x'; exact manyYear P.J.k P.J.n l (hU k) P.dpos.le F₀ (roofage Y i s) (he ▸ xP) (le_max_left ..) Z (fun i h b=> F₁ MU b i h) Q pR e hp vz a T (innerRate d) t' hr g0 uz vT (moodPair q d w J hq vq gq L.length Ns (hL.trans (Nat.mul_le_mul_right _ hrQ))) x' _ _ (safety Y s i k x').2 (hQ s) -- tune
 have hp4: ‖X₀ Vc‖ ≤ Real.exp (-10000*sites Ns):= (gV k S.depth S.enters Vc T (l.corsage.env) hCap).trans (Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_right g (show 0≤ sites Ns by unfold sites; positivity)))
 have Hc: ‖X₀ Vc-Y₀ Vc‖≤ Real.exp (-10000*sites Ns):=by refine (φ i S.depth Vc D l.corsage.env (fun x=> (l.capPrice (fun a v=> F₁ _ _ a.s (l.granted a v).far) hχ x pR.le).trans (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right _ p4)))).trans_eq (div_mul_cancel₀ _ hg.ne')
 have ℓ0:(1:ℝ) ≤ r:= by exact_mod_cast v'
 have ht: (r:ℝ) ≤ sites Ns:= by unfold sites; exact_mod_cast (hrQ.trans p4)
 have gTrade: ‖Y₀ D'‖ ≤ Real.exp (-9999):=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le (show r ≠0 from v'.ne')).mp
    apply YX.trans; rw [←Real.exp_nat_mul]; refine ((norm_le_norm_sub_add (Y₀ Vc) (X₀ Vc)).trans (add_le_add ((norm_sub_rev ..).trans_le Hc) hp4)).trans ?_
    rw [show r *(-9999:ℝ)=r+(-10000*(r:ℝ)) by ring,Real.exp_add]
    have hp:Real.exp (-10000*sites Ns) ≤ Real.exp (-10000*(r:ℝ)):= Real.exp_le_exp_of_le (by linarith)
    have hE:2 ≤ Real.exp (r:ℝ):=by linarith only [ℓ0,Real.add_one_le_exp (r:ℝ)]
    nlinarith only [hE,hp, (show 0<Real.exp (-10000*(r:ℝ)) from Real.exp_pos _)] -- tune positivity
 have hFee: ∀ x: Fields Ns, ‖F.frame x‖ ≤ (1+R)^(q^4):=fun i'=> hf.price (F₁ MU _ _ hf.far) (hχ _) i'
 have T':AtSupport false (CF.Pannier.Chancel.hyphen 0 0 F.broad∪ F.broad) D':= ((hf.atCost.refl 0 0).mono subset_union_left).mulM (hf.atCost.mono subset_union_right) -- name hyphen
 refine ⟨hf,hFee,?_⟩; change ‖X₀ D'‖≤ _; apply (norm_le_norm_sub_add _ (Y₀ D')).trans
 have h₁:=φ i S.depth D' D T'.env (fun x=>by
    have hp: ‖reflMark 0 0 F.frame x‖≤ _ := pairPrice hFee 0 x -- lemma below
    refine ((norm_mul_le ..).trans (mul_le_mul hp (hFee x) (norm_nonneg _) (by positivity))).trans ?_
    rw [← pow_add]; apply pow_le_pow_right₀ (by linarith); rw [← two_mul]; exact Nat.mul_le_mul_right _ (le_trans (show 2≤ L.length from by omega) (show L.length ≤ (More Ns).val^4 from p4)))
 have hs: ‖X₀ D'-Y₀ D'‖≤Real.exp (-9999):= (show ‖X₀ D'-Y₀ D'‖ ≤ G*D from h₁).trans ((div_mul_cancel₀ _ hg.ne').trans_le (Real.exp_le_exp_of_le (by linarith)))
 have u'': Real.exp (-9999)≤ 1/10000:=by rw [Real.exp_neg,←one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp 9999])
 exact (add_le_add hs gTrade).trans (by linarith only [u''])
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.winePair
